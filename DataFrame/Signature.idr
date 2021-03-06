module DataFrame.Signature

import public Data.List
import public Decidable.Equality

%default total

-- (::) is infixr 7
infix 3 :-
public export
record Named a where
  constructor (:-)
  name : String
  value : a

public export
mapItemType : (a -> b) -> Named a -> Named b
mapItemType p (cn :- a) = cn :- p a

public export
Sig : Type
Sig = List (Named Type)

-- for derived sequences with unnamed elements
namespace All
  public export
  data All : (Type -> Type) -> Sig -> Type where
    Nil : All p []
    (::) : p a -> All p sig -> All p ((cn :- a) :: sig)

-- for derived sequences with named elements
namespace SigF
  public export
  data SigF : (Type -> Type) -> Sig -> Type where
    Nil : SigF p []
    (::) : (e : Named (p a)) -> SigF p sig -> SigF p ((name e :- a) :: sig)

namespace InSig
  public export
  data InSig : (cn : String) -> (a : Type) -> (sig : Sig) -> Type where
    [search cn sig]
    Here : InSig cn x ((cn :- x) :: sig)
    There : InSig cn x sig -> InSig cn x ((cn' :- x') :: sig)

public export
Map : (a -> b) -> List (Named a) -> List (Named b)
Map = map . mapItemType

export
sigMapId : (sig : Sig) -> Map (\x => x) sig = sig
sigMapId [] = Refl
sigMapId ((cn :- a) :: sig) = cong ((cn :- a) ::) (sigMapId sig)

public export
insert : (cn : String) -> (a : Type) -> Sig -> Sig
insert cn a [] = [cn :- a]
insert cn a ((cn' :- a') :: sig) with (decEq cn cn')
  insert cn a ((cn  :- a') :: sig) | Yes Refl = (cn  :- a)  :: sig
  insert cn a ((cn' :- a') :: sig) | No  _    = (cn' :- a') :: insert cn a sig

public export
overrideWith : Sig -> Sig -> Sig
overrideWith lhs [] = lhs
overrideWith lhs ((cn :- a) :: rhs) = insert cn a lhs `overrideWith` rhs
