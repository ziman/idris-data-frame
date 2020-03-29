module DataFrame.Signature

import public Data.List

%default total

-- (::) is infixr 7
infix 8 :-
public export
record SigItem a where
  constructor (:-)
  name : String
  type : a

public export
mapItemType : (a -> b) -> SigItem a -> SigItem b
mapItemType p (cn :- a) = cn :- p a

public export
Sig : Type
Sig = List (SigItem Type)

namespace All
  public export
  data All : (Type -> Type) -> Sig -> Type where
    Nil : All p []
    (::) : p a -> All p sig -> All p (cn :- a :: sig)

namespace InSig
  public export
  data InSig : (cn : String) -> (a : Type) -> (sig : Sig) -> Type where
    [search cn sig]
    Here : InSig cn x (cn :- x :: sig)
    There : InSig cn x sig -> InSig cn x (cn' :- x' :: sig)

public export
Map : (a -> b) -> List (SigItem a) -> List (SigItem b)
Map = map . mapItemType

export
sigMapId : (sig : Sig) -> Map (\x => x) sig = sig
sigMapId [] = Refl
sigMapId (cn :- a :: sig) = cong ((cn :- a) ::) (sigMapId sig)
