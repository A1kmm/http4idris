module Control.Funext

-- Functional extensionality axiom. Not provable in Idris but also consistent with
-- standard axioms, so safe to define...
export
funext : (f, g : a -> b) -> ((x : a) -> f x = g x) -> f = g
funext f g = believe_me
