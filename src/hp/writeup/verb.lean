

/- naive calculations etc for english grammar.
[todo] delete unncecc stuff. -/

namespace english

-- /-- Noun phrase. -/
-- inductive np
-- | pronoun (n : number) (p : person)
-- | word (x : string) (n : number)
-- | proper (x : string) (n : number)
-- | definite : np
-- constant np.number : np → number
-- constant np.person : np → person

inductive person
| First -- i, we
| Second -- you
| Third -- they, he, she, it

inductive number
| Singular
| Plural

inductive tense
| Past
| Present
| Future

inductive aspect
| Simple
| Progressive
| Perfect
| PerfactProgressive

inductive mood
| Indicative
| Subjunctive
| Imperative
| Conditional

structure verb :=
(stem : string)
(subjunctive := stem)
(present := [stem, stem, stem ++ "s", stem])

def verb.is : verb :=
{ stem := "is"
, present := ["am", "are", "is", "are"]
, subjunctive := "be" -- note "were" is subjunctive past but not used anywhere.
}

structure verb.config :=
(person := person.Third)
(number := number.Singular)
(tense := tense.Present)
(aspect := aspect.Simple)
(mood := mood.Indicative)
-- todo also negation

def verb.conjugate : verb.config → verb → option string
| {person := person.First, number := number.Singular, tense := tense.Present, aspect := aspect.Simple, mood := mood.Indicative} v :=  v.present.nth 0
| {person := person.Second, number := number.Singular, tense := tense.Present, aspect := aspect.Simple, mood := mood.Indicative} v := v.present.nth 1
| {person := person.Third, number := number.Singular, tense := tense.Present, aspect := aspect.Simple, mood := mood.Indicative} v := v.present.nth 2
| {person := _, number := number.Plural, tense := tense.Present, aspect := aspect.Simple, mood := mood.Indicative} v := v.present.nth 3
| {person := _, number := _, tense := _, aspect := aspect.Simple, mood := mood.Subjunctive} v := some $ v.subjunctive
| {person := _, number := _, tense := _, aspect := _, mood := _} v := none -- either not defined or not implemented

end english