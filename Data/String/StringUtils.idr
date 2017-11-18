module Data.String.StringUtils

import Data.Bool.BoolTheorems
import Data.Nat.NatTheorems

%default total
%access public export

strIndex' : (str : String)
            -> (idx : Nat)
            -> {prf : Nat.LT idx (length str)}
            -> Char
strIndex' str idx =
  assert_total (prim__strIndex str (toIntNat idx))

private
chrDigit : (c : Char) -> Maybe Nat
chrDigit c = if isDigit c then Just (cast $ (ord c) - (ord '0')) else Nothing

Cast String (Maybe Nat) where
  cast s = doCast 0 0 totalLength where
    totalLength : Nat
    totalLength = length s
    
    -- TODO: Remaining length is redundant with offset.
    doCast : Nat -> Nat -> Nat -> Maybe Nat
    doCast accum offs Z = Just accum
    doCast accum offs (S lRet) = 
      ifWithProofs (ltNat offs totalLength)
        (\prfLt => do
          digit <- chrDigit (strIndex' s offs {
                     prf = natALtBIsTrueImpliesLTAB offs totalLength $
                       ltNatIsLt prfLt})
          doCast (accum * 10 + digit) (S offs) lRet
        )
        (\_ => Just accum)

private
natCast : String -> Maybe Nat
natCast = cast

private
test_cast_valid_string : (natCast "123" = Just 123)
test_cast_valid_string = Refl

private
test_cast_invalid_string : (natCast "123a" = Nothing)
test_cast_invalid_string = Refl

-- TODO: Round tripping property? Contains non-digit implies Nothing?
