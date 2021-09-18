/- This file contains an example of 'magic rewrite' widget working. -/
import hp.rewrite.equate_attr
import hp.rewrite.magic_rewrite

variables {G : Type} [group G]

example {x y z : G} (h : z = x⁻¹) : (x * y)⁻¹ * z = y⁻¹ :=
begin

end