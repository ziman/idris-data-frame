module DataFrame.Pretty

import Data.Nat
import Data.Strings
import DataFrame.Ops
import public DataFrame.DataFrame

%default total

public export
data Alignment = Left | Right

public export
record ShowOpts a where
  constructor MkShowOpts
  show : a -> String
  alignment : Alignment

toStringColumns : {sig : Sig} -> (showOpts : Annotation ShowOpts sig)
    => Columns n sig -> Vect (length sig) (Alignment, String, Vect n String)
toStringColumns {sig = []} [] = []
toStringColumns {sig = cn :- a :: sig} {showOpts = _ :- so :: _} (xs :: cols) =
  (alignment so, cn, map (show so) xs) :: toStringColumns cols

pad : Alignment -> Nat -> Char -> String -> String
pad alignment width c str =
  case cmp (length str) width of
    CmpLT d => case alignment of
      Left => str ++ pack (replicate (S d) c)
      Right => pack (replicate (S d) c) ++ str
    _ => str

layout : Vect n Nat -> Vect n (Alignment, String, Vect m String) -> Vect n (Vect (2 + m) String)
layout [] [] = []
layout (width :: widths) ((al, cn, col) :: cols) =
  (pad al width ' ' cn :: pad al width '-' "" :: map (pad al width ' ') col)
  :: layout widths cols

export
toString : {sig : Sig} -> Annotation ShowOpts sig -> DF sig -> String
toString {sig} opts (MkDF {rowCount} cols) =
    unlines . map (unwords . toList) . toList
      $ transpose (layout (map colWidth scols) scols)
  where
    scols : Vect (length sig) (Alignment, String, Vect rowCount String)
    scols = toStringColumns cols

    colWidth : (Alignment, String, Vect m String) -> Nat
    colWidth (al, cn, vals) = foldr max Z (length cn :: map length vals)

defaultOpts : {sig : Sig} -> (allShow : All Show sig) => Annotation ShowOpts sig
defaultOpts {sig = []} = []
defaultOpts {sig = cn :- a :: sig} {allShow = _ :: _} =
  cn :- MkShowOpts Prelude.show Pretty.Left :: defaultOpts

export
{sig : Sig} -> All Show sig => Show (DF sig) where
  show = toString defaultOpts . Ops.head 16

{-
df : DF ["name" :- String, "age" :- Int]
df = MkDF
  [ ["Joe", "Anne", "Lisa"]
  , [1, 2, 3]
  ]

ff : Vect k (String, Vect n String) -> Vect k Int
ff = map (\(x,xs) => foldr max 0 (map (cast . Prelude.length) $ x :: xs))

cs : Vect (List.length [("name" :- String), ("age" :- Int)]) (String, Vect (S (S (S Z))) String)
cs = toStringColumns (columns df)
-}
