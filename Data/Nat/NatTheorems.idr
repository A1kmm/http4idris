module Data.Nat.NatThereoms

%default total
%access export

-- Lemmas about Bool to support main theorems (move somewhere else?)
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

-- Theorems about Nat compare

Uninhabited (EQ = LT) where
  uninhabited Refl impossible
Uninhabited (EQ = GT) where
  uninhabited Refl impossible
Uninhabited (Interfaces.GT = LT) where
  uninhabited Refl impossible
Uninhabited (Interfaces.GT = EQ) where
  uninhabited Refl impossible
Uninhabited (LT = EQ) where
  uninhabited Refl impossible
Uninhabited (LT = Interfaces.GT) where
  uninhabited Refl impossible

natCompareSASBOImpliesCompareABO : (a : Nat)
  -> (b : Nat)
  -> (o : Ordering)
  -> compare (S a) (S b) = o
  -> compare a b = o
natCompareSASBOImpliesCompareABO a b o prf = prf

-- Theorems about Nat equality...

natSAEqSBTrueImpliesAEqBTrue : (a : Nat) -> (b : Nat) ->
                            (S a == S b = True) -> a == b = True
natSAEqSBTrueImpliesAEqBTrue a b prf = prf

natAEqBTrueImpliesEq : (a : Nat) -> (b : Nat) -> (a == b = True) -> a = b
natAEqBTrueImpliesEq Z Z _ = Refl
natAEqBTrueImpliesEq Z (S x) prf = absurd prf
natAEqBTrueImpliesEq (S x) Z prf = absurd prf
natAEqBTrueImpliesEq (S x) (S y) prf =
  eqSucc x y (natAEqBTrueImpliesEq x y (natSAEqSBTrueImpliesAEqBTrue x y prf))

natComparesAsEQImpliesEq : (a : Nat) -> (b : Nat) -> compare a b = EQ -> a = b
natComparesAsEQImpliesEq Z Z _ = Refl
natComparesAsEQImpliesEq (S _) Z prf = absurd prf
natComparesAsEQImpliesEq Z (S _) prf = absurd prf
natComparesAsEQImpliesEq (S x) (S y) prf = eqSucc x y (natComparesAsEQImpliesEq x y prf)

-- Theorems about Nat less than

natALtZIsFalse : (a : Nat) -> (a < 0) = False
natALtZIsFalse Z = Refl
natALtZIsFalse (S _) = Refl

natComparesAsLtImpliesLT : (a : Nat) -> (b : Nat) -> compare a b = LT -> LT a b
natComparesAsLtImpliesLT Z Z prf = absurd prf
natComparesAsLtImpliesLT (S x) Z prf = absurd prf
natComparesAsLtImpliesLT Z (S x) _ = LTESucc (LTEZero)
natComparesAsLtImpliesLT (S x) (S y) prf =
  LTESucc $ natComparesAsLtImpliesLT x y (natCompareSASBOImpliesCompareABO x y LT prf)

natALtBTrueImpliesComparesAsLT : (a : Nat) -> (b : Nat) -> a < b = True -> compare a b = LT
natALtBTrueImpliesComparesAsLT a b prf with (compare a b)
  natALtBTrueImpliesComparesAsLT _ _ prf | GT = absurd prf
  natALtBTrueImpliesComparesAsLT _ _ prf | EQ = absurd prf
  natALtBTrueImpliesComparesAsLT _ _ prf | LT = Refl

natALtBIsFalseImpliesComparesAsEQOrGT : (a : Nat) -> (b : Nat) -> (a < b = False) -> Either (compare a b = EQ) (compare a b = GT)
natALtBIsFalseImpliesComparesAsEQOrGT a b prf with (compare a b)
  natALtBIsFalseImpliesGTEAB _ _ _ | GT = Right Refl
  natALtBIsFalseImpliesGTEAB _ _ _ | EQ = Left Refl
  natALtBIsFalseImpliesGTEAB _ _ prf | LT = absurd prf

natALtBIsTrueImpliesLTAB : (a : Nat) -> (b : Nat) -> (a < b = True) -> LT a b
natALtBIsTrueImpliesLTAB a b prf =
  natComparesAsLtImpliesLT a b (natALtBTrueImpliesComparesAsLT a b prf)

-- Theorems about Nat <=

natALTBImpliesALTEB : (a : Nat) -> (b : Nat) -> LT a b -> LTE a b
natALTBImpliesALTEB a b prf = lteSuccLeft prf

-- Theorems about Nat <

natComparesAsGTImpliesGT : (a : Nat) -> (b : Nat) -> compare a b = GT -> GT a b
natComparesAsGTImpliesGT Z Z prf = absurd prf
natComparesAsGTImpliesGT (S _) Z _ =  LTESucc LTEZero
natComparesAsGTImpliesGT Z (S _) prf = absurd prf
natComparesAsGTImpliesGT (S x) (S y) prf = LTESucc (natComparesAsGTImpliesGT x y prf)

-- Theorems about Nat >=

natEQImpliesGTE : (a : Nat) -> (b : Nat) -> (a = b) -> GTE a b
natEQImpliesGTE a b prf = rewrite prf in lteRefl

natGTImpliesGTE : (a : Nat) -> (b : Nat) -> (GT a b) -> GTE a b
natGTImpliesGTE a b prf = lteSuccLeft prf

natComparesAsEQOrGTImpliesGTE :
  (a : Nat) ->
  (b : Nat) ->
  Either (compare a b = EQ) (compare a b = GT) ->
  GTE a b
natComparesAsEQOrGTImpliesGTE a b (Left eqPrf) =
  natEQImpliesGTE a b (natComparesAsEQImpliesEq a b eqPrf)
natComparesAsEQOrGTImpliesGTE a b (Right gtPrf) =
  natGTImpliesGTE a b (natComparesAsGTImpliesGT a b gtPrf)

natALtBIsFalseImpliesGTEAB : (a : Nat) -> (b : Nat) -> (a < b = False) -> GTE a b
natALtBIsFalseImpliesGTEAB a b prf =
  natComparesAsEQOrGTImpliesGTE a b (natALtBIsFalseImpliesComparesAsEQOrGT a b prf)
