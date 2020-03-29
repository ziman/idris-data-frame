module DataFrame.Core

import public Data.List
import public Data.Vect

import public DataFrame.Utils
import public DataFrame.Vector

%default total

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

namespace SigAll
  public export
  data SigAll : (Type -> Type) -> Sig -> Type where
    Nil : SigAll p []
    (::) : p a -> SigAll p sig -> SigAll p (cn :- a :: sig)

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
  {rowCount : Nat}
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
