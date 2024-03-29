module Data.Scientific.Parser.Simple

import Data.Fin
import Data.List1

import Text.Lexer
import Text.Lexer.Core
import Text.Parser
import Text.Parser.Core

import Data.Scientific

||| Kinds of tokens that can occur in a textual representation of a Scientific 10.
public export
data ScientificTokenKind = TDigit
                         | TSeparator
                         | TExponator
                         | TSign

public export
Show ScientificTokenKind where
  show TDigit = "TDigit"
  show TSeparator = "TSeparator"
  show TExponator = "TExponator"
  show TSign = "TSign"

public export
TokenKind ScientificTokenKind where
  TokType TDigit = Fin 10
  TokType TSeparator = ()
  TokType TExponator = ()
  TokType TSign = Sign
  tokValue TDigit "0" = 0
  tokValue TDigit "1" = 1
  tokValue TDigit "2" = 2
  tokValue TDigit "3" = 3
  tokValue TDigit "4" = 4
  tokValue TDigit "5" = 5
  tokValue TDigit "6" = 6
  tokValue TDigit "7" = 7
  tokValue TDigit "8" = 8
  tokValue TDigit "9" = 9
  tokValue TDigit _ = ?exhaustiveBecauseOfTokenMap1 -- TODO
  tokValue TSeparator _ = ()
  tokValue TExponator _ = ()
  tokValue TSign "+" = Positive
  tokValue TSign "-" = Negative
  tokValue TSign _ = ?exhaustiveBecauseOfTokenMap2 -- TODO

public export
Eq ScientificTokenKind where
  TDigit == TDigit = True
  TSeparator == TSeparator = True
  TExponator == TExponator = True
  TSign == TSign = True
  _ == _ = False

export
tokenMap : TokenMap (Token ScientificTokenKind)
tokenMap = toTokenMap
  [ (digit, TDigit)
  , (is '.', TSeparator)
  , (oneOf "eE", TExponator)
  , (oneOf "+-", TSign)
  ]

private
grammarSign : Grammar (Token ScientificTokenKind) False Sign
grammarSign = fromMaybe Positive <$> optional (match TSign)

private
grammarBeforeSeparator : Grammar (Token ScientificTokenKind) True (Fin 9)
grammarBeforeSeparator = match TDigit >>= catchZero
  where catchZero : Fin 10 -> Grammar (Token ScientificTokenKind) False (Fin 9)
        catchZero FZ = fail "expected digit between 1 and 9"
        catchZero (FS x) = pure x

private
grammarZero : Grammar (Token ScientificTokenKind) True (Scientific 10)
grammarZero = match TDigit >>= f
  where f : Fin 10 -> Grammar _ False (Scientific 10)
        f 0 = pure SciZ
        f _ = fail "expected digit 0"

private
grammarSeparator : Grammar (Token ScientificTokenKind) True (List1 (Fin 10))
grammarSeparator = match TSeparator *> some (match TDigit)

private
fixCoeff : Fin 9 -> Maybe (List1 (Fin 10)) -> Maybe (Coefficient 10)
fixCoeff x Nothing = Just $ CoeffInt x
fixCoeff x (Just y) with (unsnoc y)
  fixCoeff x (Just y) | (zs, FZ) = Nothing
  fixCoeff x (Just y) | (zs, FS z) = Just $ CoeffFloat x zs z

private
grammarCoeff : Grammar (Token ScientificTokenKind) True (Coefficient 10)
grammarCoeff = fixCoeff <$> grammarBeforeSeparator <*> optional grammarSeparator >>= maybe (fail "expected ending on digit between 1 and 9") pure

private
fixExp : List1 (Fin 10) -> Integer
fixExp = foldr1 f . map finToInteger . reverse
  where f : Integer -> Integer -> Integer
        f x i = x + 10 * i

private
grammarExponent : Grammar (Token ScientificTokenKind) True Integer
grammarExponent = match TExponator *> applySign <$> grammarSign <*> fixExp <$> some (match TDigit)
  where applySign : Sign -> Integer -> Integer
        applySign Positive = id
        applySign Negative = negate

-- TODO: Fix exponent.
-- TODO: Expect eof after zero.
||| Grammar of a Scientific 10.
export
scientificGrammar : Grammar (Token ScientificTokenKind) True (Scientific 10)
scientificGrammar = grammarZero <|> (Sci <$> grammarSign <*> grammarCoeff <*> grammarExponent)
