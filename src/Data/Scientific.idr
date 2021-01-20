module Data.Scientific
-- TODO: don't export everything publicly?

import Data.Fin
import Data.List
import Data.Vect

||| Arbitrary precision coefficient for scientific notation in base b.
||| Representants are unique regarding (==) and there are no trailing zeros.
||| For a coefficient x this holds:
|||   1 <= x < b
public export
data Coefficient : (b : Nat) -> Type where
  CoeffInt : Fin (S b) ->
             Coefficient (S (S b))
  CoeffFloat : Fin (S b) ->
               List (Fin (S (S b))) ->
               Fin (S b) ->
               Coefficient (S (S b))

public export
Eq (Coefficient b) where
  (CoeffInt x) == (CoeffInt y) = x == y
  (CoeffFloat x xs x') == (CoeffFloat y ys y') = x == y && xs == ys && x' == y'
  _ == _ = False

public export
Ord (Coefficient b) where
  compare (CoeffInt x) (CoeffInt y) = compare x y
  compare (CoeffInt x) (CoeffFloat y ys y') = case compare x y of
                                               EQ => LT
                                               comp => comp
  compare (CoeffFloat x xs x') (CoeffInt y) = case compare x y of
                                               EQ => GT
                                               comp => comp
  compare (CoeffFloat x xs x') (CoeffFloat y ys y') =
    compare (FS x :: xs `snoc` FS x') (FS y :: ys `snoc` FS y')

private
prettyShowDigit : Fin 10 -> Char
prettyShowDigit x =
  case x of
       0 => '0'
       1 => '1'
       2 => '2'
       3 => '3'
       4 => '4'
       5 => '5'
       6 => '6'
       7 => '7'
       8 => '8'
       9 => '9'

private
prettyShowCoefficient : Coefficient 10 -> String
prettyShowCoefficient (CoeffInt x) = pack [ prettyShowDigit (FS x) ]
prettyShowCoefficient (CoeffFloat x xs x') =
  pack $ [ prettyShowDigit (FS x), '.' ] ++ map prettyShowDigit xs ++ [ prettyShowDigit (FS x') ]

public export
data Sign = Positive
          | Negative

public export
Eq Sign where
  Positive == Positive = True
  Negative == Negative = True
  _ == _ = False

public export
Ord Sign where
  compare Positive Positive = EQ
  compare Positive Negative = GT
  compare Negative Positive = LT
  compare Negative Negative = EQ

private
prettyShowSign : Sign -> String
prettyShowSign s = case s of
                        Positive => ""
                        Negative => "-"

||| A scientific notation numeral in base b.
||| Representants are unique, as this type is built on top of Coefficient.
||| The numbers x represented are those which can be written as a finite sum of powers of b:
|||   x = \Sigma_{i=n}^m a_i * b^i          , {n,m : Integer; a_i : Fin b}
public export
data Scientific : (b : Nat) -> Type where
  SciZ : Scientific b
  Sci : Sign ->
        Coefficient b ->
        Integer ->
        Scientific b

public export
Eq (Scientific b) where
  SciZ == SciZ = True
  (Sci s c e) == (Sci s' c' e') = s == s' && c == c' && e == e'
  _ == _ = False

public export
Ord (Scientific b) where
  compare SciZ SciZ = EQ
  compare SciZ (Sci s _ _) = case s of
                                  Positive => LT
                                  Negative => GT
  compare (Sci s _ _) SciZ = case s of
                                  Positive => GT
                                  Negative => LT
  compare (Sci s c e) (Sci s' c' e') =
    case (s, s') of
         (Positive, Positive) => case compare e e' of
                                      EQ => compare c c'
                                      comp => comp
         (Positive, Negative) => GT
         (Negative, Positive) => LT
         (Negative, Negative) => case compare e' e of
                                      EQ => compare c' c
                                      comp => comp

export
negate : Scientific b -> Scientific b
negate SciZ = SciZ
negate (Sci s c e) = let s' = case s of
                                   Positive => Negative
                                   Negative => Positive
                     in Sci s' c e

export
abs : Scientific b -> Scientific b
abs SciZ = SciZ
abs (Sci _ c e) = Sci Positive c e

-- TODO: What happens, when Integer is negative? Low priority, since this is private.
||| The digits of an Integer, least significant first.
private
integerDigits : {b : _} -> Integer -> List (Fin (S (S b)))
integerDigits 0 = []
integerDigits x = d :: integerDigits r where
  d : Fin (S (S b))
  d = restrict (S b) x
  r : Integer
  r = x `div` natToInteger (S (S b))

||| Remove the zeros near the head of a list.
private
removeLeadingZeros : List (Fin (S (S b))) -> Maybe (Fin (S b), List (Fin (S (S b))))
removeLeadingZeros [] = Nothing
removeLeadingZeros (FZ :: xs) = removeLeadingZeros xs
removeLeadingZeros (FS x :: xs) = Just (x, xs)

private
fromDigits : List (Fin (S (S b))) -> Scientific (S (S b))
fromDigits ys =
  case removeLeadingZeros $ reverse ys of
       Nothing => SciZ
       Just (x, ys') => case removeLeadingZeros $ reverse ys' of
                            Nothing => Sci Positive (CoeffInt x) (cast $ length ys')
                            Just (x', xs) => Sci Positive (CoeffFloat x (reverse xs) x') (cast $ length ys')

export
fromFin : Fin (S (S b)) -> Scientific (S (S b))
fromFin FZ = SciZ
fromFin (FS x) = Sci Positive (CoeffInt x) 0

export
fromInteger : {b : _} -> Integer -> Scientific (S (S b))
fromInteger x = if x < 0
                   then negate $ fromIntegerPositive x
                   else fromIntegerPositive x
where
  fromIntegerPositive : Integer -> Scientific (S (S b))
  fromIntegerPositive = fromDigits . integerDigits . abs

export
fromNat : {b : _} -> Nat -> Scientific (S (S b))
fromNat = fromInteger . natToInteger

||| Single bit full adder in base (S (S b)).
private
plusBit : (op : Sign) ->
          {b : _} ->
          (carry : Bool) ->
          Fin (S (S b)) ->
          Fin (S (S b)) ->
          ((Fin (S (S b))), Bool)
plusBit op False x FZ = (x, False)
plusBit Positive True x FZ = case strengthen $ FS FZ of
                                  Left _ => (FZ, True)
                                  Right z => (z, False)
plusBit Negative True x FZ = case x of
                                  FZ => (last, True)
                                  FS z => (weaken z, False)
plusBit Positive carry x (FS y) = case strengthen $ FS x of
                                       Left _ => (fst $ plusBit Positive carry FZ (weaken y), True)
                                       Right z => plusBit Positive carry z (weaken y)
plusBit Negative carry x (FS y) = case x of
                                       FZ => (fst $ plusBit Negative carry last (weaken y), True)
                                       FS z => plusBit Negative carry (weaken z) (weaken y)

||| N bit full adder in base (S (S b)).
export
plusBits : (op : Sign) ->
           {b : _} ->
           (carry : Bool) ->
           Vect n (Fin (S (S b))) ->
           Vect n (Fin (S (S b))) ->
           (Vect n (Fin (S (S b))), Bool)
plusBits op carry [] [] = ([], carry)
plusBits op carry (x :: xs) (y :: ys) =
  let (z, carry') = plusBit op carry x y
      (zs, sign) = plusBits op carry' xs ys
  in (z :: zs, sign)

-- TODO: Add NonEmpty to result type.
||| All bits of a Coefficient, least significant first.
export
coefficientBits : Coefficient (S (S b)) -> List (Fin (S (S b)))
coefficientBits (CoeffInt x) = [FS x]
coefficientBits (CoeffFloat x xs x') = reverse $ FS x :: xs ++ [FS x']

-- TODO: get a definiton like this working:
--equalizeLength : a ->
--                 (xs : List a) ->
--                 (ys : List a) ->
--                 (Vect (max (length xs) (length ys)) a, Vect (max (length xs) (length ys)) a)
private
equalizeLength : a ->
                (n : _) ->
                (xs : List a) ->
                (ys : List a) ->
                (Vect n a, Vect n a)
equalizeLength a Z _ _ = ([],[])
equalizeLength a (S k) [] [] = let (ps, qs) = equalizeLength a k [] []
                               in (a :: ps, a :: qs)
equalizeLength a (S k) [] (y::ys) = let (ps, qs) = equalizeLength a k [] ys
                                    in (a :: ps, y :: qs)
equalizeLength a (S k) (x::xs) [] = let (ps, qs) = equalizeLength a k xs []
                                    in (x :: ps, a :: qs)
equalizeLength a (S k) (x::xs) (y::ys) = let (ps, qs) = equalizeLength a k xs ys
                                         in (x :: ps, y :: qs)

||| Wrapper for plusBits, adding padding regarding the exponent and trailing zeros.
private
plusBits' : (op : Sign) ->
            {b : _} ->
            (List (Fin (S (S b))), Integer) ->
            (List (Fin (S (S b))), Integer) ->
            (List (Fin (S (S b))), Bool)
plusBits' op (xs,xe) (ys,ye) =
  let n = max (length xs) (length ys)
      (xs'', ys'') = equalizeLength FZ n xs' ys'
      (zs, overflow) = plusBits op False (reverse xs'') (reverse ys'')
  in (toList zs, overflow) where
    xs' : List (Fin (S (S b)))
    xs' = reverse $ xs ++ replicate (integerToNat ye `minus` integerToNat xe) FZ
    ys' : List (Fin (S (S b)))
    ys' = reverse $ ys ++ replicate (integerToNat xe `minus` integerToNat ye) FZ

-- TODO: remove this or removeLeadingZeros
private
removeLeadingZeros' : List (Fin (S (S b))) -> (Nat, Maybe (Fin (S b), List (Fin (S (S b)))))
removeLeadingZeros' [] = (Z, Nothing)
removeLeadingZeros' (FZ :: xs) = let (n, res) = removeLeadingZeros' xs
                                 in (S n, res)
removeLeadingZeros' (FS x :: xs) = (Z, Just (x, xs))

||| Requires the digits to be ordered, least significant first.
||| Returns Coefficient and number of significant zeros.
private
fromDigits' : List (Fin (S (S b))) -> (Maybe (Coefficient (S (S b))), Nat)
fromDigits' ys =
  let (n, removedLeading) = removeLeadingZeros' $ reverse ys
  in case removedLeading of
          Nothing => (Nothing, n)
          Just (x, ys') => case removeLeadingZeros $ reverse ys' of
                               Nothing => (Just (CoeffInt x), n)
                               Just (x', xs) => (Just (CoeffFloat x (reverse xs) x'), n)

export
(+) : {b : _} -> Scientific (S (S b)) -> Scientific (S (S b)) -> Scientific (S (S b))
SciZ + y = y
x + SciZ = x
x@(Sci s c e) + y@(Sci s' c' e') =
  let (zs, bit) = plusBits' op (xs, e) (ys, e')
  in case op of
          Positive => let s'' = s
                          bits = if bit then [FS FZ] else [FZ]
                      in case fromDigits' $ zs ++ bits of
                              (Nothing, _) => SciZ
                              (Just c'', bitShift) => let e'' = max e e' + 1 - natToInteger bitShift
                                                      in Sci s'' c'' e''
          Negative => let s'' = if bit then s' else s
                      in case fromDigits' zs of
                              (Nothing, _) => SciZ
                              (Just c'', bitShift) => let e'' = max e e' - natToInteger bitShift
                                                      in Sci s'' c'' e''
where
  op : Sign
  op = if s == s'
          then Positive
          else Negative
  xs : List (Fin (S (S b)))
  xs = coefficientBits c
  ys : List (Fin (S (S b)))
  ys = coefficientBits c'

-- TODO
||| Multiply two Coefficients and return True in the Bool, when the product is greater than the base.
private
multCoefficents : {b : _} -> Coefficient (S (S b)) -> Coefficient (S (S b)) -> (Coefficient (S (S b)), Bool)
multCoefficents (CoeffInt x) (CoeffInt y) =
  case integerToFin res (S b) of
       Nothing => (CoeffInt $ restrict b res, True)
       Just fin => (CoeffInt fin, False)
where
  res : Integer
  res = (finToInteger x + 1) * (finToInteger y + 1) - 1
multCoefficents a@(CoeffInt x) b@(CoeffFloat y ys y') = multCoefficents b a
-- TODO: finish multCoefficents
multCoefficents (CoeffFloat x xs x') (CoeffInt y) = ?multCoefficents_rhs_2
multCoefficents (CoeffFloat x xs x') (CoeffFloat y ys y') = ?multCoefficents_rhs_3

export
(*) : {b : _} -> Scientific (S (S b)) -> Scientific (S (S b)) -> Scientific (S (S b))
SciZ * y = SciZ
x * SciZ = SciZ
(Sci s c e) * (Sci s' c' e') = Sci s'' c'' e'' where
  coefficientPair : (Coefficient (S (S b)), Bool)
  coefficientPair = multCoefficents c c'
  s'' : Sign
  s'' = if s == s'
           then Positive
           else Negative
  c'' : Coefficient (S (S b))
  c'' = fst coefficientPair
  e'' : Integer
  e'' = if snd coefficientPair
           then e + e' + 1
           else e + e'

-- -- TODO: implementations don't work because the base (S (S b)) isn't accessible in the method's context.
-- -- TODO: consider other implementations:
-- -- - Fractional might not terminate, because of infinite representation
-- -- - Integral doesn't sound like it would fit, but mod and div make still make sense
-- public export
-- Num (Scientific (S (S b))) where
--   -- (+) = (+)
--   -- (*) = (+)
--   -- fromInteger = fromInteger

-- public export
-- Neg (Scientific (S (S b))) where
--   -- negate = negate

-- public export
-- Abs (Scientific (S (S b))) where
--   -- abs = abs

||| Create string representing using scientific notation.
export
prettyShowScientific : Scientific 10 -> String
prettyShowScientific SciZ = "0"
prettyShowScientific (Sci s c e) = prettyShowSign s ++ prettyShowCoefficient c ++ prettyExponent where
  prettyExponent : String
  prettyExponent = case e of
                        0 => ""
                        x => "e" ++ show x
