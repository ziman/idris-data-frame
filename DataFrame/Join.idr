module DataFrame.Join

import public DataFrame.Signature
import public DataFrame.DataFrame

data ColNames : Sig -> List Type -> Type where
  Nil : ColNames sig []
  (::) :
    Eq a =>
    (cn : String) ->
    (0 inSig : InSig cn a sig) =>
    ColNames sig as ->
    ColNames sig (a :: as)

infix 2 ^=
record JoinOn sigL sigR where
  constructor (^=)
  {onTypes : List Type}
  colsL : ColNames sigL onTypes
  colsR : ColNames sigR onTypes

{-
SigJoin : (sigL, sigR : Sig) -> Sig
SigJoin sigL sigR = ?rhs_sj

SigInnerJoinOn : {sigL, sigR : _} -> JoinOn sigL sigR -> Sig
SigInnerJoinOn ([] ^= []) = SigJoin sigL sigR
SigInnerJoinOn (cnL :: cnsL ^= cnR :: cnsR) = ?rhs_sjo_5
-}

{-
innerJoinOn : (jo : JoinOn sig sig') -> DF sig -> DF sig' -> DF (SigJoinOn jo)
innerJoinOn jo df df' = ?rhs_ijo
-}

cnWeaken : ColNames sig ts -> ColNames ((cn :- a) :: sig) ts
cnWeaken = ?rhs_cnWeaken

record SplitSig (cns : ColNames sig ts) where
  constructor MkSplitSig
  selected : Sig
  notSelected : Sig
  restricted : ColNames selected ts

splitSig : (sig : Sig) -> (cns : ColNames sig ts) -> SplitSig cns
splitSig sig [] = MkSplitSig
  { selected = []
  , notSelected = sig
  , restricted = []
  }
splitSig sig ((::) {a} cn {inSig} cns) with (splitSig sig cns)
  _ | subSig =
    let a' = lookup cn sig inSig
      in MkSplitSig
        { selected = (cn :- a') :: subSig.selected
        , notSelected = delete cn subSig.notSelected
        , restricted = cn :: cnWeaken subSig.restricted
        }

{-
splitSig : (sig : Sig) -> (cns : ColNames sig ts) -> SplitSig cns
splitSig [] [] = MkSplitSig
  { selected = []
  , notSelected = []
  , restricted = []
  }
splitSig sig [] = MkSplitSig
  { selected = []
  , notSelected = sig
  , restricted = []
  }
splitSig [] (_ :: _) impossible
splitSig ((cnL :- ty) :: sig) (cnR :: cns) with (decEq cnL cnR)
  splitSig ((cn :- ty) :: sig) (cn :: cns) | Yes Refl = ?rhs
  splitSig ((cnL :- ty) :: sig) (cnR :: cns) | No nope = ?rhs2
splitSig (sh :: sig) (cn :: cns) = ?rhsI
-}
