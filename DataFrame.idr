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
  (::) : Vect n a -> Columns n sig -> Columns n (cn :- a :: sig)

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
extract (xs :: cols)  Here      = xs
extract (xs :: cols) (There pf) = extract cols pf

infix 3 ^.
(^.) :
    (df : DF sig)
    -> (cn : String)
    -> {auto pf : InSig cn a sig}
    -> Vect (rowCount df) a
(^.) df cn {pf} = extract (columns df) pf

df : DF ["name" :- String, "age" :- Int]
df = MkDF 3
    [ ["Joe", "Anne", "Lisa"]
    , [1, 2, 3]
    ]

infix 3 <&>
(<&>) : Functor f => f a -> (a -> b) -> f b
(<&>) x f = map f x

(++) : {sig : Sig} -> Columns m sig -> Columns n sig -> Columns (m + n) sig
(++) {sig = []} [] [] = []
(++) {sig = cn :- a :: sig} (xs :: cs) (xs' :: cs') = (xs ++ xs') :: cs ++ cs'

reverse : {sig : Sig} -> Columns n sig -> Columns n sig
reverse {sig = []} [] = []
reverse {sig = cn :- a :: sig} (xs :: cs) = reverse xs :: reverse cs

parseColumns : Vect n String -> Either String (Columns n sig)
parseColumns rows = ?rhs

parseCsv : (sig : Sig) -> List String -> Either String (DF sig)
parseCsv sig [] = Left "no header found"
parseCsv sig (hdr :: rs) = MkDF (length rs) . reverse <$> (parseColumns $ fromList rs)

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
