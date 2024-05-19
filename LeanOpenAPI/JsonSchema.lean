/-  Copyright (C) 2023 The OpenAPI library contributors.

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <https://www.gnu.org/licenses/>.
-/

import Lean.Data.Json
import LeanOpenAPI.Std

/-! This file implements a version of parsing JsonSchema. -/

namespace LeanOpenAPI

namespace JsonSchema

/-! References -/

structure Reference where
  (file : Option String) (tokens : List String)
deriving DecidableEq, Hashable

namespace Reference

def toString (r : Reference) : String :=
  r.tokens.foldl (init := "#") (· ++ "/" ++ tokenEncode ·)
where
  tokenEncode (s : String) :=
    s.replace (pattern := "~") (replacement := "~0")
    |>.replace (pattern := "/") (replacement := "~1")
instance : ToString Reference := ⟨Reference.toString⟩

def fromString (s : String) : Except String Reference := do
  let idx := s.nextUntil (· = '#') 0
  let file := s.extract 0 idx
  let path := s.extract idx s.endPos
  let segs := path.drop 1 |>.splitOn (sep := "/") |>.drop 1 |>.map tokenDecode
  return ⟨if file.isEmpty then none else some file, segs⟩
where
  tokenDecode (s : String) :=
    s.replace (pattern := "~1") (replacement := "/")
    |>.replace (pattern := "~0") (replacement := "~")

private def resolvePointer (j : Lean.Json) (p : List String) : Except String Lean.Json := do
  match p with
  | [] => return j
  | t::p =>
  match j with
  | .obj m =>
      let some j' := m.find compare t | throw s!"object does not contain key {t}"
      resolvePointer j' p
  | .arr a =>
      let some i := t.toNat? | throw s!"referencing array element, but reference token {t} is not a number"
      let some j' := a[i]? | throw s!"reference token {t} out of range of array"
      resolvePointer j' p
  | _ => throw "referencing a value that is not an object or array"

def thenIdx (i : Nat) : Reference → Reference
| {file, tokens} => {file, tokens := (tokens.concat (ToString.toString i)) }
def thenKey (k : String) : Reference → Reference
| {file, tokens} => {file, tokens := tokens.concat k }

end Reference

structure LeanEmbedding where
  (type fromJson toJson : Lean.Ident)

structure State where
  curRef : Reference
  curName : Lean.Ident
  done : Std.HashMap Reference LeanEmbedding

def SchemaElabM := ExceptT String <| StateT State Lean.Elab.Command.CommandElabM

namespace SchemaElabM

instance : Monad SchemaElabM := inferInstanceAs (Monad (ExceptT _ _))
instance : MonadLift (Except String) SchemaElabM where
  monadLift e := show ExceptT _ _ _ from liftM e

end SchemaElabM

inductive «Type»
| integer | number | boolean | string
| array | object | null
deriving DecidableEq, Lean.ToJson, Lean.FromJson

def Type.toLeanEmbedding (c : «Type») : Schema :=
  match c with
  | .integer => integer
  | .number  => number
  | .boolean => boolean
  | .string  => string
  | .array   => array any
  | .object  => objectMap fun _ => any

def type : SchemaM «Type» := JsonSchema.ofLeanJson

end CoreSchema

/- TODO: schema schemas should be specified via recursive structures,
but Lean structures currently don't have good enough support
for nested inductives for this to not be hugely painful. -/

def CoreSchema := Lean.Json
deriving Inhabited, Repr

namespace CoreSchema

structure Res where
  docs : Option String
  type : Lean.Syntax.Term
  toString : Lean.Syntax.Term
  fromString : Lean.Syntax.Term
  default : Option Lean.Syntax.Term
deriving Inhabited, Repr

def toRes (s : CoreSchema) : Lean.Elab.TermElabM Res := do
  let j : Lean.Json := s
  match j.getObj? with
  | .error _ => fallback j
  | .ok m =>
  match m.find compare "type" with
  | none => fallback j
  | some type =>
  match Lean.FromJson.fromJson? (α := «Type») type with
  | .error _ => fallback j
  | .ok ty =>
  let analyze : Option (Lean.Term × Lean.Term × Lean.Term) ←
    (match ty with
      | .integer  => do
        return some ( ← `(Int)            , ← `(toString)        , ← `(Option.toMonad ∘ String.toInt?))
      | .number   => do
        return some ( ← `(Lean.JsonNumber), ← `(toString)        , ← `((Lean.Json.parse · >>= Lean.Json.getNum?)))
      | .string   => do
        return some ( ← `(String)         , ← `(id)              , ← `(pure))
      | .boolean  => do
        return some ( ← `(Bool)           , ← `(toString)        , ← `(Bool.fromString))
      | .object   => do
        return some ( ← `(Lean.Json)      , ← `(Lean.Json.pretty), ← `(Lean.Json.parse))
      | .array    => pure none
    )
  let some (type, toString, fromString) := analyze
    | return ← fallback j
  let docs := some j.toYaml
  return { docs, type, toString, fromString, default }
where fallback (j) := do return {
  docs := some (j.toYaml)
  type := ← `(String)
  toString := ← `(id)
  fromString := ← `(pure)
  default := none
}

end CoreSchema

def coreSchema : SchemaM CoreSchema := any
