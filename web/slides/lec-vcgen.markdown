% Floyd-Hoare Logic & Verification Conditions
% Ranjit Jhala, UC San Diego 
% April 16, 2013

## A Small Imperative Language

~~~~~{.haskell}
data Var    

data Exp   

data Pred  
~~~~~

## A Small Imperative Language

~~~~~{.haskell}
data Com = Asgn  Var Expr
         | Seq   Com Com
         | If    Exp Com Com
         | While Pred Exp Com
         | Skip
~~~~~

## Verification Condition Generation

Use the `State` monad to log individual loop invariant requirements

~~~~~{.haskell}
type VC = State [Pred]  -- validity queries for SMT solver
~~~~~

## Top Level Verification Function

The top level verifier, takes: 

- **Input**  : precondition `p`, command `c` andpostcondition `q`

- **Output** : `True` iff `{p} c {q}` is a valid Hoare-Triple

~~~~~{.haskell}
verify       :: Pred -> Com -> Pred -> Bool

verify p c q    = all smtValid queries
  where 
    (q', conds) = runState (vcgen q c) []  
    queries     = p `implies` q' : conds 
~~~~~

## Verification Condition Generator

~~~~~{.haskell}
vcgen :: Pred -> Com -> VC Pred

vcgen (Skip) q  
  = return q
vcgen (Asgn x e) q  
  = return $ q `subst` (x, e)
vcgen (Seq s1 s2) q
  = vcgen s1 =<< vcgen s2 q
vcgen (If b c1 c2) q
  = do q1    <- vcgen c1 q
       q2    <- vcgen c2 q
       return $ (b `implies` q1) `And` (Not b `implies` q2)
vcgen (While i b c) q 
  = do q'    <- vcgen c i 
       sideCondition $ (i `And` b)     `implies` q' 
       sideCondition $ (i `And` Not b) `implies` q  
       return $ i                            
~~~~~

## `vcgen` Helper Logs All Side Conditions

~~~~~{.haskell}
sideCond :: Pred -> VC ()
sideCond p = modify $ \conds -> p : conds 
~~~~~
