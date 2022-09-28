module Exercises.File4

import Data.Vect

%default total
%hide concat

data DescVar : Type where
  Var   : DescVar
  Zero  : DescVar
  One   : DescVar
  Plus  : DescVar -> DescVar -> DescVar
  Times : DescVar -> DescVar -> DescVar

ToType : DescVar -> Type -> Type
ToType Var ty = ty
ToType Zero ty = Void
ToType One ty = Unit
ToType (Plus x y) ty = Either (ToType x ty) (ToType y ty)
ToType (Times x y) ty = Pair (ToType x ty) (ToType y ty)

-----------------
-- Intro Exercise
-----------------

IsFunctor : (a -> b) -> (ctx : DescVar) -> ToType ctx a -> ToType ctx b
IsFunctor f Var x = f x
IsFunctor f Zero x = absurd x
IsFunctor f One x = x
IsFunctor f (Plus y z) x = bimap (IsFunctor f y) (IsFunctor f z) x
IsFunctor f (Times y z) x = bimap (IsFunctor f y) (IsFunctor f z) x

Three : DescVar
Three = Var `Times` (Var `Times` Var)

ThreeTy : Type -> Type
ThreeTy = ToType Three

MkThree : (a : Type) -> a -> a -> a -> ThreeTy a
MkThree a x y z = (x, y, z)

get1 : ThreeTy a -> a
get1 (x, y, z) = x

get2 : ThreeTy a -> a
get2 (x, y, z) = y

get3 : ThreeTy a -> a
get3 (x, y, z) = z

------------------------------
-- Multiple Variables Exercise
------------------------------

namespace Variables
  data Context : Nat -> Type where
    Var   : Fin n -> Context n
    Zero  : Context n
    One   : Context n
    Plus  : Context n -> Context n -> Context n
    Times : Context n -> Context n -> Context n

  ToType : Context n -> Vect n Type  -> Type
  ToType (Var x) xs = index x xs
  ToType Zero xs = Void
  ToType One xs = Unit
  ToType (Plus x y) xs = Either (ToType x xs) (ToType y xs)
  ToType (Times x y) xs = Pair (ToType x xs) (ToType y xs)

  CLeft : Context 2
  CLeft = Var 0

  CRight : Context 2
  CRight = Var 1

  CEither : Context 2
  CEither = CLeft `Plus` CRight

  CFst : Context 2
  CFst = Var 0

  CSnd : Context 2
  CSnd = Var 1

  CPair : Context 2
  CPair = CFst `Times` CSnd

  CFirst : Context 3
  CFirst = Var 0

  CSecond : Context 3
  CSecond = Var 1

  CThird : Context 3
  CThird = Var 2

  CTri : Context 3
  CTri = CFirst `Plus` (CSecond `Plus` CThird)

  CEBLeft : Context 2
  CEBLeft = Var 0

  CEBRight : Context 2
  CEBRight = Var 1

  CEBBoth : Context 2
  CEBBoth = Var 0 `Times` Var 1

  CEitherBoth : Context 2
  CEitherBoth = CEBLeft `Plus` (CEBRight `Plus` CEBBoth)

  CMkTriple : Context 3
  CMkTriple = Var 0 `Times` (Var 1 `Times` Var 2)

  CTriple : Context 3
  CTriple = CMkTriple

---------------------
-- Fixpoints Exercise
---------------------

namespace Recursive
  public export
  data CFT : Nat -> Type where
    Var   : Fin n -> CFT n
    Zero  : CFT n
    One   : CFT n
    Plus  : CFT n -> CFT n -> CFT n
    Times : CFT n -> CFT n -> CFT n
    Mu    : CFT (S n) -> CFT n

  record Fix (f : Type -> Type) where
    constructor In
    unFix : Inf (f (Fix f))

  export
  ToType : CFT n -> Vect n Type  -> Type
  ToType (Var x) xs = index x xs
  ToType Zero xs = Void
  ToType One xs = Unit
  ToType (Plus x y) xs = Either (ToType x xs) (ToType y xs)
  ToType (Times x y) xs = Pair (ToType x xs) (ToType y xs)
  ToType (Mu x) xs = Fix (\self => ToType x (self :: xs))

  ----------------------------
  -- Define Nat, List and Tree
  ----------------------------

  NatDesc : CFT Z
  NatDesc = Mu(One `Plus` Var 0)

  NatTy : Type
  NatTy = ToType NatDesc []

  ListDesc : CFT (S n)
  ListDesc = Mu(One `Plus` (Var 1 `Times` Var 0))

  ListTy : Type -> Type
  ListTy ty = ToType ListDesc [ty]

  TreeDesc : CFT (S n)
  TreeDesc = Mu(One `Plus` (Var 1 `Times` (Var 0 `Times` Var 0)))

  TreeTy : Type -> Type
  TreeTy ty = ToType TreeDesc [ty]

  --------------------------
  -- Define the constructors
  --------------------------

  Z : NatTy
  Z = In $ Left ()

  S : NatTy -> NatTy
  S x = In $ Right x

  Empty : (a : Type) -> ListTy a
  Empty a = In $ Left ()

  Cons : (a : Type) -> a -> ListTy a -> ListTy a
  Cons a x xs = In $ Right (x, xs)

  Leaf : (a : Type) -> TreeTy a
  Leaf a = In $ Left ()

  Branch : (a : Type) -> a -> TreeTy a -> TreeTy a -> TreeTy a
  Branch a x l r = In $ Right (x, l, r)

  -----------------------------------------------------------------------------------------
  -- Then write addition for our custom Nat, length for List and inorder : Tree a -> List a
  -----------------------------------------------------------------------------------------

  add : NatTy -> NatTy -> NatTy
  add (In (Left x)) y = y
  add (In (Right x)) y = In $ Right $ add x y

  length : ListTy a -> NatTy
  length (In (Left x)) = In $ Left x
  length (In (Right (x, xs))) = In $ Right $ length xs

  concat : ListTy a -> ListTy a -> ListTy a
  concat (In (Left x)) y = y
  concat (In (Right (x, xs))) y = In $ Right (x, concat xs y)

  partial
  inorder : TreeTy a -> ListTy a
  inorder (In (Left x)) = In $ Left ()
  inorder (In (Right (x, l, r))) =
    let ls = inorder l
        rs = inorder r
    in In $ Right (x, concat ls rs)
