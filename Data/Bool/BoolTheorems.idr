module Data.Bool.BoolTheorems

%default total
%access export

public export
ifWithProofs : (x : Bool) -> ((x = True) -> a) -> (not x = True -> a) -> a
ifWithProofs True f _ = f Refl
ifWithProofs False _ f = f Refl

AOrFalseIsA : (a : Bool) -> a || False = a
AOrFalseIsA True = Refl
AOrFalseIsA False = Refl

NotAEqNotBImpliesAEqB : (a : Bool) -> (b : Bool) -> (not a = not b) -> (a = b)
NotAEqNotBImpliesAEqB True True _ = Refl
NotAEqNotBImpliesAEqB False False _ = Refl
NotAEqNotBImpliesAEqB True False prf = absurd prf
NotAEqNotBImpliesAEqB False True prf = absurd prf

NotNotCancels : (a : Bool) -> a = True -> not (not a) = True
NotNotCancels True prf = prf
NotNotCancels False prf = prf
