module DataFrame.IO

import System.File
import Data.Strings

import DataFrame.Columns
import DataFrame.Utils

import public DataFrame.DataFrame

public export
interface CsvValue a where
  fromString : String -> Either String a

export
CsvValue String where
  fromString str = Right str

export
CsvValue Int where
  fromString str = Right (cast str)  -- TODO

public export
CsvSig : Sig -> Type
CsvSig = All CsvValue

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
parseCsv sig (hdr :: rs) = MkDF <$> (parseRows 1 $ fromList rs)

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
