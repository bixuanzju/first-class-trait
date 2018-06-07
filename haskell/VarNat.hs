data Value = IntV  Int
           | BoolV Bool
           deriving Eq

type Env = [(String, Value)]

-- AST
data Exp = Num Int
         | Add Exp Exp
         | Sub Exp Exp
         | Mult Exp Exp
         | Div Exp Exp
         | Var String
         | Decl String Exp Exp

-- Evaluator
evaluate :: Exp -> Env -> Maybe Value
evaluate (Num n) _ = Just (IntV n)
evaluate (Add a b) env = do
  (IntV av) <- evaluate a env
  (IntV bv) <- evaluate b env
  return (IntV (av + bv))
evaluate (Sub a b) env = do
  (IntV av) <- evaluate a env
  (IntV bv) <- evaluate b env
  return (IntV (av - bv))
evaluate (Mult a b) env = do
  (IntV av) <- evaluate a env
  (IntV bv) <- evaluate b env
  return ((IntV (av * bv)))
evaluate (Div a b) env = do
  (IntV av) <- evaluate a env
  (IntV bv) <- evaluate b env
  return (IntV (av `div` bv))
evaluate (Var s) env = lookup s env
evaluate (Decl n a b) env = do
  v <- evaluate a env
  evaluate b ((n, v) : env)



-- Pretty printer
pretty :: Exp -> String
pretty (Num n) = show n
pretty (Add exp1 exp2) = "(" ++ pretty exp1 ++ " + " ++ pretty exp2 ++ ")"
pretty (Sub exp1 exp2) = "(" ++ pretty exp1 ++ " - " ++ pretty exp2 ++ ")"
pretty (Mult exp1 exp2) = "(" ++ pretty exp1 ++ " * " ++ pretty exp2 ++ ")"
pretty (Div exp1 exp2) = "(" ++ pretty exp1 ++ " / " ++ pretty exp2 ++ ")"
pretty (Var s) = s
pretty (Decl n e1 e2) = "var " ++ n ++ " = " ++ pretty e1 ++ "; " ++ pretty e2
