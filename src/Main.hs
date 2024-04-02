{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# HLINT ignore "Use camelCase" #-}

module Main where

import Control.Monad (foldM)
import Control.Monad.ST (ST, runST)
import Data.Data (Typeable)
import Data.Field.Galois (Prime)
import Data.Foldable (for_)
import qualified Data.Map as Map
import Data.Maybe (catMaybes, fromJust, fromMaybe)
import Data.Propagator
import Data.Propagator.Cell (unify)
import Data.Propagator.Num (PropagatedNum (cplus, ctimes))
import Data.STRef (STRef, newSTRef, readSTRef, writeSTRef)
import Data.Traversable (for)
import Debug.Trace (trace, traceM)
import Factors (factors)
import GHC.TypeLits (KnownNat)
import Snarkl.Common (Assgn (Assgn), Var (Var))
import Snarkl.Constraint (ConstraintSystem (..), SimplifiedConstraintSystem (SimplifiedConstraintSystem), constraint_vars)
import Snarkl.Constraint.Constraints (CoeffList (..), Constraint (..))
import Snarkl.Errors (ErrMsg (ErrMsg), failWith)
import Snarkl.Field (P_BN128)
import Snarkl.Toplevel (Comp, R1CS (r1cs_num_vars, r1cs_out_vars), Result (Result), SimplParam, Witness (..), comp_interp, compileCompToTexp, compileTExpToR1CS, num_constraints, sat_r1cs)
import Text.PrettyPrint.Leijen.Text (pretty)

data Env s k = Env
  { vars :: Map.Map Var (Cell s k)
  }

--------------------------------------------------------------------------------

mkEnv :: [Var] -> ST s (Env s (Prime p))
mkEnv vs = do
  b <- for vs $ \v -> do
    c <- cell
    pure (v, c)
  pure $ Env $ Map.fromList b

instance Propagated (Prime p)

instance (KnownNat p) => PropagatedNum (Prime p)

constraintToPropagator :: (KnownNat p) => Env s (Prime p) -> Constraint (Prime p) -> ST s ()
constraintToPropagator Env {..} (CAdd r (CoeffList xs)) = do
  sumCell <- known (-r)
  let f acc (v, c) = do
        let vCell = fromMaybe (error "constraintToProt.vCell1") $ Map.lookup v vars
        p <- do
          cCell <- known c
          p <- cell
          ctimes cCell vCell p
          pure p
        acc' <- cell
        cplus acc p acc'
        pure acc'
  (seedCell, xs') <- case xs of
    (v, c) : rest -> do
      p <- cell
      cCell <- known c
      let vCell = fromMaybe (error "constraintToProp.seedCell") $ Map.lookup v vars
      ctimes cCell vCell p
      pure (p, rest)
    [] -> error "constraintToPropagator"
  s <- foldM f seedCell xs'
  unify s sumCell
constraintToPropagator Env {..} mc@(CMult (ca, va) (cb, vb) (cc, vc)) =
  traceM (show mc) >> do
    a <- do
      let aCell = fromMaybe (error "constraintToProp.aCell") $ Map.lookup va vars
      if ca == 1
        then pure aCell
        else do
          p <- cell
          c <- known ca
          ctimes c aCell p
          pure p
    b <- do
      let bCell = fromMaybe (error "constraintToProp.bCell") $ Map.lookup vb vars
      if cb == 1
        then pure bCell
        else do
          p <- cell
          c <- known cb
          ctimes c bCell p
          pure p
    c <- case vc of
      Just v -> do
        let vCell = fromMaybe (error "constraintToProp.vCell") $ Map.lookup v vars
        if cc == 1
          then pure vCell
          else do
            p <- cell
            c <- known cc
            traceM $ show cc <> " * " <> show vc <> " = pc"
            ctimes c vCell p
            pure p
      Nothing -> known cc
    ctimes a b c
constraintToPropagator Env {..} (CMagic _ vs f) = pure () -- error "No Magic Constraints yet..."

mkPropagatorNetwork :: (KnownNat p) => ConstraintSystem (Prime p) -> ST s (Env s (Prime p))
mkPropagatorNetwork cs@ConstraintSystem {..} = do
  env <- mkEnv $ constraint_vars cs_constraints
  traceM $ show cs
  for_ cs_constraints $ constraintToPropagator env
  pure env

solveConstraintSystem ::
  (KnownNat p) =>
  Assgn (Prime p) ->
  ConstraintSystem (Prime p) ->
  Assgn (Prime p)
solveConstraintSystem (Assgn initialAssignments) cs = runST $ do
  env <- mkPropagatorNetwork cs
  for_ (Map.toList initialAssignments) $ \(v, r) -> do
    let vCell = fromJust $ Map.lookup v (vars env)
    traceM $ "writing " ++ show r ++ " to " ++ show v
    write vCell r
  bindings <- for (Map.toList (vars env)) $ \(v, c) -> do
    r <- content c
    pure $ (v, r)
  traceM $ "bindings: " ++ show bindings
  pure $ Assgn . Map.fromList . catMaybes $ map sequence bindings

--------------------------------------------------------------------------------
-- vendored code
--------------------------------------------------------------------------------

-- \| For a given R1CS and inputs, calculate a satisfying assignment.
wit_of_cs ::
  (KnownNat p) =>
  [Prime p] ->
  Map.Map Var (Prime p) ->
  SimplifiedConstraintSystem (Prime p) ->
  Witness (Prime p)
wit_of_cs inputs privateInputs (SimplifiedConstraintSystem cs) =
  let public_in_vars = cs_public_in_vars cs
   in if length public_in_vars /= length inputs
        then
          failWith $
            ErrMsg
              ( "expected "
                  ++ show (length public_in_vars)
                  ++ " input(s)"
                  ++ " but got "
                  ++ show (length inputs)
                  ++ " input(s)"
              )
        else
          let inputAssignments = Assgn $ privateInputs `Map.union` Map.fromList (zip public_in_vars inputs)
           in Witness
                { witness_assgn = solveConstraintSystem inputAssignments cs,
                  witness_in_vars = public_in_vars,
                  witness_out_vars = cs_out_vars cs,
                  witness_num_vars = cs_num_vars cs
                }

execute ::
  (KnownNat p) =>
  (Typeable ty) =>
  [SimplParam] ->
  Comp ty (Prime p) ->
  [Prime p] ->
  Map.Map String (Prime p) ->
  Result (Prime p)
execute simpl mf inputs privateInputs =
  let texpPkg = compileCompToTexp mf
      (r1cs, constraintSystem, privateInputVars) = compileTExpToR1CS simpl texpPkg
      privateAssignments =
        trace
          (show constraintSystem)
          $ Map.fromList
          $ [ (var, val)
              | (k, val) <- Map.toList privateInputs,
                (k', var) <- Map.toList privateInputVars,
                k == k'
            ]
      out_var = case r1cs_out_vars r1cs of
        [a] -> a
        _ -> error "one output variable required"
      wit@(Witness {witness_assgn = Assgn m}) = wit_of_cs inputs privateAssignments constraintSystem
      out = case Map.lookup out_var m of
        Nothing ->
          failWith $
            ErrMsg
              ( "output variable "
                  ++ show out_var
                  ++ "not mapped, in \n  "
                  ++ show wit
              )
        Just out_val -> out_val
      -- Interpret the program using the executable semantics and
      -- the input assignment (a subset of 'wit').
      -- Output the return value of 'e'.
      out_interp = comp_interp mf inputs privateInputs
      nw = r1cs_num_vars r1cs
      ng = num_constraints r1cs
      result = out_interp == out && sat_r1cs wit r1cs
   in if result
        then Result result nw ng out r1cs wit
        else
          failWith $
            ErrMsg $
              "interpreter result "
                ++ show out_interp
                ++ " differs from actual result "
                ++ show out

main :: IO ()
main = do
  print $ execute @P_BN128 [] factors [2, 3, 4] Map.empty

-- main'

simpleProp1 :: ST s (Cell s Int, Cell s Int, Cell s Int)
simpleProp1 = do
  a <- cell
  b <- cell
  c <- cell
  ctimes a b c
  pure (a, b, c)

simpleProp2 :: ST s (Cell s Int, Cell s Int, Cell s Int)
simpleProp2 = do
  a <- cell
  b <- cell
  c <- cell
  ctimes a b c
  pure (a, b, c)

main' :: IO ()
main' = print $ runST $ do
  (a, b, c) <- simpleProp1
  (d, e, f) <- simpleProp2
  p <- cell
  ctimes c f p
  write a 2
  write b 3
  write d 4
  write e 5
  content p