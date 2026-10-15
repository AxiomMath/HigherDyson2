module

public meta import Lean

/-!
# The `higher_dyson_2` tag attribute

This file declares the `higher_dyson_2` attribute, which takes a single string argument naming a
tag and records that the declaration it is attached to formalizes the entity with that tag. The
attribute has no effect on elaboration.
-/

public meta section

open Lean

/-- The syntax of the `higher_dyson_2` attribute: the attribute name followed by a string literal
giving the tag. -/
syntax (name := higher_dyson_2) "higher_dyson_2 " str : attr

initialize Lean.registerBuiltinAttribute {
  name  := `higher_dyson_2
  descr := "marks a declaration as formalizing a blueprint entity"
  add   := fun _ _ _ => pure ()
}

end
