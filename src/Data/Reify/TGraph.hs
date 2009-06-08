{-# LANGUAGE GADTs, ExistentialQuantification, FlexibleContexts
           , UndecidableInstances
  #-}
{-# OPTIONS_GHC -Wall #-}

module Data.Reify.TGraph
  ( ShowF(..), Id, V(..), Bind(..), Graph(..)
  ) where

-- import Data.IsTy

-- | Identifiers
type Id = Int

-- | Typed variables
data V ty a = V Id (ty a)

-- | Typed binding pair, parameterized by variable and node type
-- constructors. 
data Bind ty n = forall a. Bind (V ty a) (n (V ty) a)

class ShowF f where
  showF :: f a -> String                -- maybe Show a => 

instance ShowF (V ty) where
  -- showF (V i t) = parens $ show i ++ "::" ++ show t
  showF (V i _) = 'x' : show i

-- parens :: String -> String
-- parens = ("(" ++) . (++ ")")

instance Show (V ty a) where show = showF

instance ShowF (n (V ty)) => Show (Bind ty n) where
  show (Bind v n) = showF v ++" = "++ showF n

-- | Graph, described by bindings and a root variable
data Graph ty n a = Graph [Bind ty n] (V ty a)

-- We could generalize V out of Bind and Graph.


instance (ShowF (n (V ty)), Show (V ty a)) => Show (Graph ty n a) where
  show (Graph netlist start) = "let " ++ show netlist ++ " in " ++ show start
