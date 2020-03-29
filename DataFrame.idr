module DataFrame

import System.File
import Data.Strings
import public Data.List
import public Data.Vect

import public DataFrame.Utils
import public DataFrame.Vector

%default total

public export
interface CsvValue a where
  fromString : String -> Either String a

export
CsvValue String where
  fromString str = Right str

export
CsvValue Int where
  fromString str = Right (cast str)  -- TODO

-- (::) is infixr 7
infix 8 :-
public export
record SigItem where
  constructor (:-)
  name : String
  type : Type

public export
Sig : Type
Sig = List SigItem

namespace CsvSig
  public export
  data CsvSig : Sig -> Type where
    Nil : CsvSig []
    (::) : CsvValue a -> CsvSig sig -> CsvSig (cn :- a :: sig)

public export
record Column n a where
  constructor MkColumn
  name : String
  values : Vect n a

namespace Columns
  public export
  data Columns : Nat -> Sig -> Type where
    Nil : Columns n Nil
    (::) : Vect n a -> Columns n sig -> Columns n (cn :- a :: sig)

public export
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

export
extract :
    Columns rowCount sig
    -> InSig cn a sig
    -> Vect rowCount a
extract (xs :: cols)  Here      = xs
extract (xs :: cols) (There pf) = extract cols pf

infix 3 ^.
export
(^.) :
    (df : DF sig)
    -> (cn : String)
    -> {auto pf : InSig cn a sig}
    -> Vect (rowCount df) a
(^.) df cn {pf} = extract (columns df) pf

export
(++) : {sig : Sig} -> Columns m sig -> Columns n sig -> Columns (m + n) sig
(++) {sig = []} [] [] = []
(++) {sig = cn :- a :: sig} (xs :: cs) (xs' :: cs') = (xs ++ xs') :: cs ++ cs'

export
reverse : {sig : Sig} -> Columns n sig -> Columns n sig
reverse {sig = []} [] = []
reverse {sig = cn :- a :: sig} (xs :: cs) = reverse xs :: reverse cs

export
empty : {sig : Sig} -> Columns 0 sig
empty {sig = []} = []
empty {sig = cn :- a :: sig} = [] :: empty

parseCells : {sig : Sig} -> (csvSig : CsvSig sig) => Int -> List String -> Either String (Columns 1 sig)
parseCells {sig = []} {csvSig = []} rowNr [] = Right []
parseCells {sig = []} {csvSig = []} rowNr (_ :: _) = Left $ "row " ++ show rowNr ++ ": too many columns"
parseCells {sig = cn :- a :: sig} {csvSig = _ :: csvSig} rowNr (cell :: cells) = do
  cellParsed <- case fromString cell of
    Left err => Left $ "row " ++ show rowNr ++ ": " ++ err
    Right value => Right value
  cellsParsed <- parseCells rowNr cells
  pure ([cellParsed] :: cellsParsed)

parseRow : {sig : Sig} -> CsvSig sig => Int -> String -> Either String (Columns 1 sig)
parseRow rowNr row = parseCells rowNr cells
  where
    cells : List String
    cells = split (== ',') row  -- TODO: actual CSV parsing

parseRows : {sig : Sig} -> CsvSig sig => Int -> Vect n String -> Either String (Columns n sig)
parseRows rowNr [] = Right empty
parseRows rowNr (row :: rows) = do
  rowParsed <- parseRow rowNr row
  rowsParsed <- parseRows (rowNr + 1) rows
  pure (rowParsed ++ rowsParsed)

parseCsv : (sig : Sig) -> CsvSig sig => List String -> Either String (DF sig)
parseCsv sig [] = Left "no header found"
parseCsv sig (hdr :: rs) = MkDF (length rs) <$> (parseRows 1 $ fromList rs)

readFileLines : String -> IO (Either String (List String))
readFileLines fname =
  readFile fname <&> \case
    Left err => Left (show err)
    Right str => Right (lines str)

export
readCsv : String -> (sig : Sig) -> CsvSig sig => IO (Either String (DF sig))
readCsv fname sig =
  readFileLines fname <&> \case
    Left err => Left err
    Right lines => parseCsv sig lines
