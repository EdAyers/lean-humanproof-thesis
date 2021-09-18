
import .prisms .interaction_monad

universes u v w

/-- Generator monad over a state σ. -/
meta inductive gen (σ : Type) : Type → Type
| lift {α} : interaction_monad σ α → gen α
| join {α} : list (gen α) → gen α
| orelse {α} : gen α → gen α → gen α
| bind {α β} : gen α → (α → gen β) → gen β

open interaction_monad

namespace gen

variables {α β σ : Type}

meta instance : monad (gen σ) :=
{ pure := λ α x, gen.lift $ λ s, result.success x s
, bind := λ α β x f, gen.bind x f
}

meta instance : alternative (gen σ) :=
{ failure := λ α, gen.lift $ λ s, result.exception none none s
, orelse := λ α a b, gen.orelse a b
}

meta def append : gen σ α → gen σ α → gen σ α
| (gen.join a) (gen.join b) := gen.join (a ++ b)
| (gen.join a) y := gen.join (a ++ [y])
| x (gen.join b) := gen.join ([x] ++ b)
| x y := gen.join [x,y]

meta instance : has_append (gen σ α) := ⟨append⟩

meta inductive volcano (σ : Type) : Type → Type
| pure {α} : (σ × α) → volcano α
| zero {α} : volcano α
| join {α}: list (volcano α) → volcano α
| orelse {α}: volcano α → volcano α → volcano α
| bind {α β}: volcano α → (α → gen σ β) → volcano β

meta def volcano.thunk : gen σ α → σ → volcano σ α
| l s := volcano.bind (volcano.pure (s,())) (λ _, l)

meta def volcano.append : volcano σ α → volcano σ α → volcano σ α
| (volcano.join a) (volcano.join b) := volcano.join (a ++ b)
| (volcano.join a) y := volcano.join (a ++ [y])
| x (volcano.join b) := volcano.join ([x] ++ b)
| x y := volcano.join [x,y]

meta def run : Π {α}, gen σ α → σ → volcano σ α
| α (gen.lift r) s :=
  match r s with
  | (result.success a s) := volcano.pure (s,a)
  | (result.exception _ _ _) := volcano.zero
  end
| α (gen.join xs) s := volcano.join $ list.map (λ a, run a s) $ xs
| α (gen.orelse a b) s := volcano.orelse (run a s) $ (run b s)
| α (gen.bind a f) s := volcano.bind (run a s) f

@[derive_prisms]
meta inductive volcano_status (σ α : Type)
| extinct : volcano_status
| erupt : list (σ × α) → volcano σ α → volcano_status

open volcano_status

meta def volcano_status.join : list (volcano_status σ α) → volcano_status σ α
| vs :=
  match list.unzip $ list.filter_map as_erupt $ vs with
  | ([], _) := extinct
  | (ls, vs) := erupt (list.join ls) $ volcano.join vs
  end

meta def volcano.step_core : Π {α}, volcano σ α → volcano_status σ α
| α (volcano.pure sx) := erupt [sx] (volcano.zero)
| α (volcano.zero) := extinct
| α (volcano.join vs) := volcano_status.join $ volcano.step_core <$> vs
| α (volcano.orelse a b) :=
  match volcano.step_core a with
  | (erupt l a) := erupt l (volcano.orelse a b)
  | extinct := volcano.step_core b
  end
| α (volcano.bind a f) :=
  match volcano.step_core a with
  | (erupt l a) := erupt [] $ volcano.join $ (list.map (λ p : σ × _, (run (f p.2) p.1)) $ l) ++ [volcano.bind a f]
  | extinct := extinct
  end

meta def volcano.next : volcano σ α → list (σ × α)
| a := match volcano.step_core a with
       | (extinct) := []
       | (erupt sx b) := sx
       end

meta def volcano.step : volcano σ α → list (σ × α) × volcano σ α
| a := match volcano.step_core a with
       | extinct := ([], volcano.zero)
       | (erupt l v) := (l,v)
       end

meta def volcano.take : nat → volcano σ α → list (σ × α)
| 0 r := []
| n r :=
  match volcano.step_core r with
  | (erupt xs v) := xs ++ volcano.take (n - (list.length xs)) v
  | done := []
  end

meta def volcano.take_while (f : (σ × α) → bool) : volcano σ α → list (σ × α)
| r :=
  match volcano.step_core r with
  | (erupt xs v) :=
    let l := list.take_while (λ x, f x = true) xs in
    if l.length = xs.length then xs ++ volcano.take_while v else l
  | done := []
  end

meta instance {m : Type → Type} [monad m] : has_monad_lift (interaction_monad σ) (gen σ) :=
{ monad_lift := @gen.lift _}

meta def reflect : option (α × gen σ α) → gen σ α
| none := failure
| (some (a,x)) := pure a ++ x

meta def observe : gen σ α → interaction_monad σ α
| x s :=
  match (run x s).take 1 with
  | ((s,x) :: t) := result.success x s
  | _ := result.exception none none s
  end

meta def observeMany : nat → gen σ α → σ → list (interaction_monad.result σ α)
| n x s := list.map (λ p : σ × α, result.success p.2 p.1) $ volcano.take n (run x s)

meta def observeWhile (f : α → interaction_monad σ bool) : gen σ α → σ → list (result σ α)
| g s := list.map (λ p : σ × α, result.success p.2 p.1) $ volcano.take_while (λ ⟨s,x⟩, ff <| (result.get (f x s))) $ run g s

meta def returnopt : option α → gen σ α
| (some a) := pure a
| none := failure

meta def of_list : list α → gen σ α :=
gen.join ∘ list.map pure

meta def unfold : (α → option (list β × α)) → α → gen σ β
| f init := (returnopt (f init)) >>= λ ⟨b,a⟩, of_list b ++ unfold f a

meta def nats : gen σ nat := unfold (λ a, some ([a], a+1)) 0

meta def pairs : gen σ α → gen σ β → gen σ (α × β)
| a b := a >>= λ a, prod.mk a <$> b

/-- Generates the prime numbers. -/
meta def primes : gen σ nat :=
@unfold (nat × list nat) nat σ (λ ⟨x,ps⟩, some $ if list.all ps (λ p, x % p ≠ 0) then ([x], (x+1, list.cons x ps)) else ([], (x+1, ps)) ) (2,[])

meta def fibo : gen σ nat :=
@unfold (nat × nat) _ _ (λ ⟨x,y⟩, some ([x],(y,x+y))) (1,1)

/- EXAMPLES: -/
-- #eval list.filter_map result.get $ observeMany 5 nats ()
-- #eval list.filter_map result.get $ observeMany 50 (pairs nats nats) ()
-- #eval list.filter_map result.get $ observeMany 100 primes ()

end gen

