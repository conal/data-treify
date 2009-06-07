
-- From TGraph.hs, line 14, 06/05/2009 05:19:00 PM:

-- | Typed binding pair, parameterized by variable and node type
-- constructors. 
data Bind n v where
  Bind :: v a -> n v a -> Bind n v

-- | Graph, described by bindings and a root variable
data Graph n v a = Graph [Bind n v] (v a)
