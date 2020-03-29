module DataFrame.Signature

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

namespace InSig
  public export
  data InSig : (cn : String) -> (a : Type) -> (sig : Sig) -> Type where
    [search cn sig]
    Here : InSig cn x (cn :- x :: sig)
    There : InSig cn x sig -> InSig cn x (cn' :- x' :: sig)
