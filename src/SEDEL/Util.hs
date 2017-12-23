module SEDEL.Util where

import SEDEL.Source.Syntax

import Data.List (foldl', foldl1')
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Name

-- | Change the sort of a name.
translate :: Name a -> Name b
translate (Fn x y) = Fn x y
translate (Bn x y) = Bn x y

-- Utility for parsing

evar :: String -> Expr
evar = Var . s2n

tvar :: String -> Type
tvar = TVar . s2n

ebind :: String -> Expr -> Bind TmName Expr
ebind n = bind (s2n n)

elam :: String -> Expr -> Expr
elam b e = Lam (ebind b e)

dlam :: (String, Type) -> Expr -> Expr
dlam (s, t) b = DLam (bind (s2n s, embed t) b)

tforall :: (String,  Type) -> Type -> Type
tforall (s, t) b = DForall (bind (s2n s, embed t) b)

eapp :: Expr -> Expr -> Expr
eapp = App

etapp :: Expr -> Type -> Expr
etapp = TApp

mkRecds :: [(Label, Expr)] -> Expr
mkRecds [] = Top
mkRecds ((l, e):r) = foldl' (\t (l', e') -> Merge t (DRec l' e')) (DRec l e) r

mkRecds' :: [TmBind] -> Expr
mkRecds' = foldl1' Merge . map DRec'

mkRecdsT :: [(Label, Type)] -> Type
mkRecdsT [] = TopT
mkRecdsT ((l, e):r) = foldl (\t (l', e') -> And t (SRecT l' e')) (SRecT l e) r

mkArr :: Type -> [Type] ->Type
mkArr = foldr Arr

mkForall :: Type -> [(TyName, Embed Type)] -> Type
mkForall = foldr (\b t -> DForall (bind b t))

eletr :: String -> Type -> Expr -> Expr -> Expr
eletr s t e b = Letrec (bind (s2n s, embed (Just t)) (e, b))


elet :: String -> Expr -> Expr -> Expr
elet s e b = Letrec (bind (s2n s, embed Nothing) (e, b))

transNew :: Type -> [Expr] -> Expr
transNew ty es =
  eletr
    "self"
    ty
    (foldl1'
       Merge
       (map
          (\tm ->
             case tm of
               Pos p (Remove e l t') -> Pos p (Remove (App e (evar "self")) l t')
               -- hack for trait excluding
               _ -> App tm (evar "self"))
          es))
    (evar "self")
