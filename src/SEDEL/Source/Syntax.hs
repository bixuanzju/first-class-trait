{-# LANGUAGE DeriveGeneric, MultiParamTypeClasses, TemplateHaskell, FlexibleInstances #-}

module SEDEL.Source.Syntax where

import           SEDEL.Common

import           Data.Text.Prettyprint.Doc (Pretty)
import qualified Data.Text.Prettyprint.Doc as Pretty
import           GHC.Generics (Generic)
import           Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.TH
import           Text.Megaparsec
import Data.Maybe (fromMaybe)


-- | Modules
data Module = Module
  { moduleEntries :: [SDecl]
  , mainExpr      :: SDecl
  } deriving (Show, Generic)

-- | Declarations other than traits
data SDecl
  = DefDecl TmBind
  | TypeDecl TypeBind
  deriving (Show, Generic)

type RawName = String

data Trait = TraitDef
  { selfType      :: (RawName, Type)
  , traitSuper    :: [Expr]
  , retType       :: Maybe Type
  , traitBody     :: [TmBind]
  } deriving (Show, Generic)


-- f A1,...,An (x1: t1) ... (xn: tn): t = e
-- If t is provided, then e can mention f
data TmBind = TmBind
  { bindName            :: RawName                   -- f
  , bindTyParams        :: [(TyName, Type)]          -- A1, ..., An
  , bindParams          :: [(TmName, Maybe Type)]    -- x1: t1, ..., xn: tn
  , bindRhs             :: Expr                      -- e
  , bindRhsTyAscription :: Maybe Type                -- t
  , isOverride          :: Bool
  } deriving (Show, Generic)

-- type T[A1, ..., An] = t
data TypeBind = TypeBind
  { typeBindName   :: RawName            -- T
  , typeBindParams :: [(TyName, Kind)]   -- A1, ..., An
  , typeBindRhs    :: Type               -- t
  } deriving (Show, Generic)


type TmName = Name Expr
type TyName = Name Type

-- Expression
data Expr = Anno Expr Type
          | Var TmName
          | App Expr Expr
          | Lam (Bind TmName Expr)
          | Letrec (Bind (TmName, Embed (Maybe Type)) (Expr, Expr))
            -- ^ let expression, possibly recursive
          | DLam (Bind (TyName, Embed Type) Expr)
          | TApp Expr Type
          | DRec Label Expr
          | Acc Expr Label
          | Remove Expr Label (Maybe Type)
          | Merge Expr Expr
          | LitV Double
          | BoolV Bool
          | StrV String
          | PrimOp Operation Expr Expr
          | If Expr Expr Expr
          | Top
          -- practical matters for surface language
          | Pos SourcePos Expr
          -- ^ marked source position, for error messages
          | LamA (Bind (TmName, Embed Type) Expr)
          -- ^ Not exposed to users, for internal use
          | Bot
          -- The following should disappear after desugaring
          | AnonyTrait Trait
          | DRec' TmBind
  deriving (Show, Generic)

type Label = String
data Type = NumT
          | BoolT
          | StringT
          | Arr Type Type
          | And Type Type
          | TVar TyName
          | DForall (Bind (TyName, Embed Type) Type)
          | SRecT Label Type
          | TopT
          | OpAbs (Bind (TyName, Embed Kind) Type)
          -- ^ Type-level abstraction: "type T A = t" becomes "type T = \A : *. t",
          | OpApp Type Type
          -- ^ Type-level application: t1 t2

  deriving (Show, Generic)

-- Kinds k := * | k -> k
data Kind = Star | KArrow Kind Kind deriving (Eq, Show, Generic)


instance Pretty (Name a) where
    pretty v = Pretty.pretty (name2String v)


-- Unbound library instances

$(makeClosedAlpha ''SourcePos)

instance Alpha Type
instance Alpha Expr
instance Alpha Trait
instance Alpha SDecl
instance Alpha TmBind
instance Alpha TypeBind
instance Alpha Kind


instance Subst b SourcePos where
  subst _ _ = id
  substs _ = id

instance Subst Expr Type
instance Subst Expr Kind
instance Subst Expr ArithOp
instance Subst Expr LogicalOp
instance Subst Expr Operation
instance Subst Expr CompOp
instance Subst Expr Trait
instance Subst Expr SDecl
instance Subst Expr TmBind
instance Subst Expr TypeBind

instance Subst Expr Expr where
  isvar (Var v) = Just (SubstName v)
  isvar _ = Nothing

instance Subst Type Expr
instance Subst Type Trait
instance Subst Type Operation
instance Subst Type LogicalOp
instance Subst Type CompOp
instance Subst Type ArithOp
instance Subst Type SDecl
instance Subst Type TmBind
instance Subst Type TypeBind
instance Subst Type Kind


instance Subst Type Type where
  isvar (TVar v) = Just (SubstName v)
  isvar _ = Nothing


-- | Partial inverse of Pos
unPosExpr :: Expr -> Maybe SourcePos
unPosExpr (Pos p _) = Just p
unPosExpr _         = Nothing

-- | Tries to find a Pos anywhere inside a term
unPosDeep :: Expr -> Maybe SourcePos
unPosDeep = unPosExpr

-- | Tries to find a Pos inside a term, otherwise just gives up.
unPosFlaky :: Expr -> SourcePos
unPosFlaky t =
  fromMaybe (SourcePos "unknown location" (mkPos 0) (mkPos 0)) (unPosDeep t)
