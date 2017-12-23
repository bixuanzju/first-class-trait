data Type
  = TInt
  | TBool
  deriving (Eq, Show)

data Value = IntV  Int
           | BoolV Bool
           deriving Eq

type TEnv = [(String,Type)]

type Env = [(String, Value)]

type TFunEnv = [(String, (Type, Type))]


-- AST
data Program = Program FunEnv Exp

type FunEnv = [(String, Function)]

data Function = Function (String, Type) Exp

data Exp = Num Int
         | Add Exp Exp
         | Sub Exp Exp
         | Mult Exp Exp
         | Div Exp Exp
         | B Bool
         | If Exp Exp Exp
         | Eq Exp Exp
         | Lt Exp Exp
         | Var String
         | Decl String Exp Exp
         | Call String Exp
         | And Exp Exp
         | Or Exp Exp


-- Evaluator
evaluate :: Exp -> Env -> FunEnv -> Maybe Value
evaluate e en fenv = eval e en
  where
    eval :: Exp -> Env -> Maybe Value
    eval (Num n) _ = Just (IntV n)
    eval (Add a b) env = do
      (IntV av) <- eval a env
      (IntV bv) <- eval b env
      return (IntV (av + bv))
    eval (Sub a b) env = do
      (IntV av) <- eval a env
      (IntV bv) <- eval b env
      return (IntV (av - bv))
    eval (Mult a b) env = do
      (IntV av) <- eval a env
      (IntV bv) <- eval b env
      return ((IntV (av * bv)))
    eval (Div a b) env = do
      (IntV av) <- eval a env
      (IntV bv) <- eval b env
      return (IntV (av `div` bv))
    eval (B b) _ = Just (BoolV b)
    eval (If e1 e2 e3) env = do
      (BoolV f) <- eval e1 env
      a <- eval e2 env
      b <- eval e3 env
      return (if f then a else b)
    eval (Eq a b) env = do
      (IntV av) <- eval a env
      (IntV bv) <- eval b env
      return (BoolV (av == bv))
    eval (Lt a b) env = do
      (IntV av) <- eval a env
      (IntV bv) <- eval b env
      return (BoolV (av < bv))
    eval (Var s) env = lookup s env
    eval (Decl n a b) env = do
      v <- eval a env
      eval b ((n, v) : env)
    eval (Call fun arg) env = do
      Function (n, _) body <- lookup fun fenv
      v <- eval arg env
      eval body ((n, v) : env)
    eval (And e1 e2) env = do
      (BoolV e1') <- eval e1 env
      (BoolV e2') <- eval e1 env
      return (BoolV (e1' && e2'))
    eval (Or e1 e2) env = do
      (BoolV e1') <- eval e1 env
      (BoolV e2') <- eval e1 env
      return (BoolV (e1' || e2'))

-- Type checker
tcheck :: Exp -> TEnv -> TFunEnv -> Maybe Type
tcheck e tenv ftenv = tcheck' e tenv
  where
    tcheck' :: Exp -> TEnv -> Maybe Type
    tcheck' (Num _) _ = Just TInt
    tcheck' (Add a b) env =
      case (tcheck' a env, tcheck' b env) of
        (Just TInt, Just TInt) -> Just TInt
        _ -> Nothing
    tcheck' (Sub a b) env =
      case (tcheck' a env, tcheck' b env) of
        (Just TInt, Just TInt) -> Just TInt
        _ -> Nothing
    tcheck' (Mult a b) env =
      case (tcheck' a env, tcheck' b env) of
        (Just TInt, Just TInt) -> Just TInt
        _ -> Nothing
    tcheck' (Div a b) env =
      case (tcheck' a env, tcheck' b env) of
        (Just TInt, Just TInt) -> Just TInt
        _ -> Nothing
    tcheck' (B _) _ = Just TBool
    tcheck' (If e1 e2 e3) env =
      case (tcheck' e1 env) of
        Just TBool ->
          case (tcheck' e2 env, tcheck' e3 env) of
            (Just t1, Just t2)
              | t1 == t2 -> Just t1
            _ -> Nothing
        _ -> Nothing
    tcheck' (Eq a b) env =
      case (tcheck' a env, tcheck' b env) of
        (Just TInt, Just TInt) -> Just TBool
        _ -> Nothing
    tcheck' (Lt a b) env =
      case (tcheck' a env, tcheck' b env) of
        (Just TInt, Just TInt) -> Just TBool
        _ -> Nothing
    tcheck' (Var s) env = lookup s env
    tcheck' (Decl v e1 e2) env =
      case tcheck' e1 tenv of
        Just t -> tcheck' e2 ((v, t) : tenv)
        Nothing -> Nothing
    tcheck' (Call name arg) env = do
      t <- tcheck' arg tenv
      (t1, t2) <- lookup name ftenv
      if t1 == t
        then return t2
        else Nothing
    tcheck' (And a b) env =
      case (tcheck' a env, tcheck' b env) of
        (Just TBool, Just TBool) -> Just TBool
        _ -> Nothing
    tcheck' (Or a b) env =
      case (tcheck' a env, tcheck' b env) of
        (Just TBool, Just TBool) -> Just TBool
        _ -> Nothing


-- Pretty printer
pretty :: Exp -> String
pretty (Num n) = show n
pretty (Add exp1 exp2) = "(" ++ pretty exp1 ++ " + " ++ pretty exp2 ++ ")"
pretty (Sub exp1 exp2) = "(" ++ pretty exp1 ++ " - " ++ pretty exp2 ++ ")"
pretty (Mult exp1 exp2) = "(" ++ pretty exp1 ++ " * " ++ pretty exp2 ++ ")"
pretty (Div exp1 exp2) = "(" ++ pretty exp1 ++ " / " ++ pretty exp2 ++ ")"
pretty (B b) = show b
pretty (If e1 e2 e3) = "(if " ++ pretty e1 ++ " then " ++ pretty e2 ++ " else " ++ pretty e3 ++ ")"
pretty (Eq exp1 exp2) = "(" ++ pretty exp1 ++ " == " ++ pretty exp2 ++ ")"
pretty (Lt exp1 exp2) = "(" ++ pretty exp1 ++ " < " ++ pretty exp2 ++ ")"
pretty (Var s) = s
pretty (Decl n e1 e2) = "var " ++ n ++ " = " ++ pretty e1 ++ "; " ++ pretty e2
pretty (Call n arg) = n ++ "(" ++ pretty arg ++ ")"
pretty (And exp1 exp2) = "(" ++ pretty exp1 ++ " && " ++ pretty exp2 ++ ")"
pretty (Or exp1 exp2) = "(" ++ pretty exp1 ++ " || " ++ pretty exp2 ++ ")"
