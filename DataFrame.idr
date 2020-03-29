module Main

import System.File
import Data.List
import Data.Vect
import Data.Strings
import Decidable.Equality

%default total

interface CsvValue a where
  fromString : String -> Either String a

-- (::) is infixr 7
infix 8 :-
record Named a where
  constructor (:-)
  name : String
  type : a

Sig : Type
Sig = List (Named Type)

record Column n a where
  constructor MkColumn
  name : String
  values : Vect n a

data Columns : Nat -> Sig -> Type where
  Nil : Columns n Nil
  (::) : Named (Vect n a) -> Columns n sig -> Columns n (cn :- a :: sig)

record DF (sig : Sig) where
  constructor MkDF
  rowCount : Nat
  columns : Columns rowCount sig

namespace InSig
  public export
  data InSig : (cn : String) -> (a : Type) -> (sig : Sig) -> Type where
    [search cn sig]
    Here : InSig cn x (cn :- x :: sig)
    There : InSig cn x sig -> InSig cn x (cn' :- x' :: sig)

extract :
    Columns rowCount sig
    -> InSig cn a sig
    -> Vect rowCount a
extract (cn :- xs :: cols) Here = xs
extract (cn :- xs :: cols) (There pf) = extract cols pf

infix 3 ^.
(^.) :
    (df : DF sig)
    -> (cn : String)
    -> {auto pf : InSig cn a sig}
    -> Vect (rowCount df) a
(^.) df cn {pf} = extract (columns df) pf

df : DF ["name" :- String, "age" :- Int]
df = MkDF 3
    [ "name" :- ["Joe", "Anne", "Lisa"]
    , "age"  :- [1, 2, 3]
    ]

infix 3 <&>
(<&>) : Functor f => f a -> (a -> b) -> f b
(<&>) x f = map f x

parseCsv : (sig : Sig) -> List String -> Either String (DF sig)
parseCsv sig lines = ?rhs

readFileLines : String -> IO (Either String (List String))
readFileLines fname =
  readFile fname <&> \case
    Left err => Left (show err)
    Right str => Right (lines str)

readCsv : String -> (sig : Sig) -> IO (Either String (DF sig))
readCsv fname sig =
  readFileLines fname <&> \case
    Left err => Left err
    Right lines => parseCsv sig lines

main : IO ()
main = putStrLn "hello world"
