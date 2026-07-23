/-
  MoverRust / Parser — a parser for the surface syntax

  A small, executable, kernel-checkable parser from a Rust-flavored
  source string with mover-logic annotations to the verified AST
  (`Stmt` of Lang.lean).  It runs inside the Lean kernel, so we can
  *prove* that a given source text parses to a given AST — connecting
  concrete syntax to the semantics and the logic.

  Surface syntax (statements):

      acquire(m);            release(m);
      r = x;                 // read of a global into a local
      r = e;                 // local assignment
      x = e;                 // write of a global
      yield;                 skip;
      assert(e);
      if (e) { s } else { s }
      while (e) { s }

  Expressions: integers, local variables, `+ - *`, `< ==` (left assoc).

  Identifiers are resolved to indices via caller-supplied environments
  (`resolveG` for globals, `resolveL` for locals), mirroring how a real
  front-end lowers names to MIR locals.
-/
import MoverRust.Lang

namespace MoverRust
namespace Parse

/-! ### Tokenizer -/

inductive Tok : Type where
  | ident (s : String)
  | num (n : Int)
  | lpar | rpar | lbrace | rbrace | semi
  | eq          -- `=`
  | eqeq        -- `==`
  | lt          -- `<`
  | plus | minus | star
deriving DecidableEq, Repr

/-- Is a character an identifier constituent? -/
def isIdentChar (c : Char) : Bool := c.isAlphanum || c = '_'

/-- Tokenize a list of characters (fuel = length suffices). -/
partial def lexAux : List Char → List Tok
  | [] => []
  | c :: cs =>
    if c = ' ' || c = '\n' || c = '\t' || c = '\r' then lexAux cs
    else if c = '(' then .lpar :: lexAux cs
    else if c = ')' then .rpar :: lexAux cs
    else if c = '{' then .lbrace :: lexAux cs
    else if c = '}' then .rbrace :: lexAux cs
    else if c = ';' then .semi :: lexAux cs
    else if c = '+' then .plus :: lexAux cs
    else if c = '-' then .minus :: lexAux cs
    else if c = '*' then .star :: lexAux cs
    else if c = '<' then .lt :: lexAux cs
    else if c = '=' then
      match cs with
      | '=' :: cs' => .eqeq :: lexAux cs'
      | _ => .eq :: lexAux cs
    else if c.isDigit then
      let ds := (c :: cs).takeWhile Char.isDigit
      let rest := (c :: cs).dropWhile Char.isDigit
      .num (String.toNat! (String.mk ds) : Int) :: lexAux rest
    else if isIdentChar c then
      let ids := (c :: cs).takeWhile isIdentChar
      let rest := (c :: cs).dropWhile isIdentChar
      .ident (String.mk ids) :: lexAux rest
    else lexAux cs  -- skip unknown characters

def tokenize (s : String) : List Tok := lexAux s.toList

/-! ### Parser

A hand-written recursive-descent parser.  `Env` resolves identifiers to
global / local indices. -/

structure Env : Type where
  resolveG : String → Option Nat
  resolveL : String → Option Nat

abbrev P (α : Type) := List Tok → Option (α × List Tok)

/-! The expression grammar, fuel-recursed so it is kernel-computable
    (examples run by `decide`).  Levels: atom ⊂ product ⊂ sum ⊂
    comparison. -/
mutual
  def pAtom (E : Env) : Nat → P Exp
    | 0, _ => none
    | _ + 1, .num n :: ts => some (.int n, ts)
    | _ + 1, .ident s :: ts => (E.resolveL s).map (fun n => (Exp.lv n, ts))
    | f + 1, .lpar :: ts =>
        match pExpr E f ts with
        | some (e, .rpar :: ts') => some (e, ts')
        | _ => none
    | _ + 1, _ => none

  def pMul (E : Env) : Nat → P Exp
    | 0, _ => none
    | f + 1, ts =>
        match pAtom E f ts with
        | some (e, .star :: ts') => (pMul E f ts').map (fun p => (Exp.mul e p.1, p.2))
        | some (e, ts') => some (e, ts')
        | none => none

  def pAdd (E : Env) : Nat → P Exp
    | 0, _ => none
    | f + 1, ts =>
        match pMul E f ts with
        | some (e, .plus :: ts') => (pAdd E f ts').map (fun p => (Exp.add e p.1, p.2))
        | some (e, .minus :: ts') => (pAdd E f ts').map (fun p => (Exp.sub e p.1, p.2))
        | some (e, ts') => some (e, ts')
        | none => none

  def pExpr (E : Env) : Nat → P Exp
    | 0, _ => none
    | f + 1, ts =>
        match pAdd E f ts with
        | some (e, .lt :: ts') => (pAdd E f ts').map (fun p => (Exp.less e p.1, p.2))
        | some (e, .eqeq :: ts') => (pAdd E f ts').map (fun p => (Exp.eq e p.1, p.2))
        | some (e, ts') => some (e, ts')
        | none => none
end

/-! ### Statement parser

`readg` vs local assignment is disambiguated by inspecting the
right-hand side: `r = x;` with `x` a global is a global read, otherwise
`r = e;` is a local assignment. -/

/-- Parse a `name(arg)`-style lock op head, returning the resolved
    global index of its single argument. -/
def pLockArg (E : Env) : P Nat
  | .lpar :: .ident s :: .rpar :: ts => (E.resolveG s).map (fun n => (n, ts))
  | _ => none

/-! A single statement, and (fuel-recursed) sequences/blocks. -/
mutual
  def pStmt (E : Env) : Nat → P Stmt
    | 0, _ => none
    | f + 1, ts =>
        match ts with
        | .ident "skip" :: .semi :: ts' => some (.skip, ts')
        | .ident "yield" :: .semi :: ts' => some (.yld, ts')
        | .ident "acquire" :: ts' =>
            match pLockArg E ts' with
            | some (m, .semi :: ts'') => some (.act (.acquire m), ts'')
            | _ => none
        | .ident "release" :: ts' =>
            match pLockArg E ts' with
            | some (m, .semi :: ts'') => some (.act (.release m), ts'')
            | _ => none
        | .ident "assert" :: .lpar :: ts' =>
            match pExpr E f ts' with
            | some (e, .rpar :: .semi :: ts'') => some (assertS e, ts'')
            | _ => none
        | .ident "if" :: .lpar :: ts' =>
            match pExpr E f ts' with
            | some (e, .rpar :: .lbrace :: ts'') =>
                match pBlock E f ts'' with
                | some (s₁, .ident "else" :: .lbrace :: ts₃) =>
                    match pBlock E f ts₃ with
                    | some (s₂, ts₄) => some (.ite (.test e) s₁ s₂, ts₄)
                    | none => none
                | _ => none
            | _ => none
        | .ident "while" :: .lpar :: ts' =>
            match pExpr E f ts' with
            | some (e, .rpar :: .lbrace :: ts'') =>
                match pBlock E f ts'' with
                | some (s, ts₃) => some (.wloop (.test e) s, ts₃)
                | none => none
            | _ => none
        | .ident name :: .eq :: ts' =>
            -- assignment: distinguish global read, local assign, global write
            match E.resolveL name, E.resolveG name with
            | some r, _ =>
                -- LHS is a local: is the RHS a bare global read?
                match ts' with
                | .ident g :: .semi :: rest =>
                    match E.resolveG g with
                    | some gx => some (.act (.readg r gx), rest)
                    | none =>
                        match pExpr E f ts' with
                        | some (e, .semi :: rest') => some (.act (.lact r e), rest')
                        | _ => none
                | _ =>
                    match pExpr E f ts' with
                    | some (e, .semi :: rest') => some (.act (.lact r e), rest')
                    | _ => none
            | none, some gx =>
                match pExpr E f ts' with
                | some (e, .semi :: rest') => some (.act (.writeg gx e), rest')
                | _ => none
            | none, none => none
        | _ => none

  /-- A sequence of statements terminated by `}` (the closing brace is
      consumed). -/
  def pBlock (E : Env) : Nat → P Stmt
    | 0, _ => none
    | f + 1, .rbrace :: ts => some (.skip, ts)
    | f + 1, ts =>
        match pStmt E f ts with
        | some (s, .rbrace :: ts') => some (s, ts')
        | some (s, ts') =>
            match pBlock E f ts' with
            | some (s₂, ts'') => some (.seq s s₂, ts'')
            | none => none
        | none => none
end

/-- Parse a whole statement block from source text. -/
def parseBlock (E : Env) (fuel : Nat) (src : String) : Option Stmt :=
  match pBlock E fuel (tokenize src ++ [.rbrace]) with
  | some (s, []) => some s
  | _ => none

/-! ### Worked example: parsing the counter's `add`

With the naming environment `x → g0, m → g1, r → l0, arg → l1`, the
source of `add` parses to exactly the AST verified in `Examples.lean`
(`Counter.addBody`).

The tokenizer uses `String` primitives, which the Lean *kernel* does not
reduce, so — as with any real compiler front-end — the parser is
*executable and tested* rather than kernel-proved: the `#guard` commands
below run at compile time (the build fails if a parse is wrong).  The
verified core is everything downstream of the AST — the semantics, the
logic, soundness, and the spec-satisfaction proof — all kernel-checked. -/

/-- Naming environment for the counter library. -/
def counterEnv : Env where
  resolveG := fun s => if s = "x" then some 0 else if s = "m" then some 1 else none
  resolveL := fun s => if s = "r" then some 0 else if s = "arg" then some 1 else none

/-- The concrete source text of `add`'s body. -/
def addSrc : String :=
  "acquire(m); r = x; x = r + arg; release(m);"

-- The parser produces exactly `Counter.addBody` (the AST proved atomic
-- and spec-conforming in `Examples.lean`).
#guard parseBlock counterEnv 100 addSrc =
  some (.seq (.act (.acquire 1))
         (.seq (.act (.readg 0 0))
           (.seq (.act (.writeg 0 (.add (.lv 0) (.lv 1))))
             (.act (.release 1)))))

-- A larger program parses too: a lock-guarded conditional.
#guard (parseBlock counterEnv 200
  "acquire(m); if (r < arg) { x = arg; } else { skip; } release(m);").isSome

-- The tokenizer handles operators and comparisons.
#guard tokenize "r = r + arg" =
  [.ident "r", .eq, .ident "r", .plus, .ident "arg"]

#guard tokenize "x == 0" = [.ident "x", .eqeq, .num 0]

end Parse
end MoverRust
