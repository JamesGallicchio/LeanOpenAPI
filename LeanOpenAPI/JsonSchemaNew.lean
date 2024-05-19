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

inductive Reference
| pointer (tokens : List String)

namespace Reference

def toString : Reference → String
| pointer toks =>
  toks.foldl (· ++ "/" ++ tokenEncode ·) "#"
where
  tokenEncode (s : String) :=
    s.replace (pattern := "~") (replacement := "~0")
    |>.replace (pattern := "/") (replacement := "~1")
instance : ToString Reference := ⟨Reference.toString⟩

def fromString (s : String) : Except String Reference := do
  unless s.startsWith "#" do
    throw "expected fragment, starting with #"
  let segs := s.drop 1 |>.splitOn (sep := "/") |>.drop 1 |>.map tokenDecode
  return .pointer segs
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
| pointer toks => pointer (toks.concat (ToString.toString i))
def thenKey (k : String) : Reference → Reference
| pointer toks => pointer (toks.concat k)

end Reference

def SchemaM := ExceptT String <| ReaderT Lean.Json <| ReaderT Reference <| ReaderT Lean.Json Id

namespace SchemaM

def run (m : SchemaM α) (j : Lean.Json) : Except String α := m j ⟨[]⟩ j

@[inline] def topJson : SchemaM Lean.Json :=
  fun top _ _ => Except.ok top
@[inline] def curJson : SchemaM Lean.Json :=
  fun _ _ cur => Except.ok cur
@[inline] def curRef : SchemaM Reference :=
  fun _ ref _ => Except.ok ref
@[inline] def throw (e : String) : SchemaM α :=
  fun _ ref _ => .error s!"{ref}: {e}"
@[inline] def withState (r : Reference) (j : Lean.Json) (s : SchemaM α) : SchemaM α :=
  fun top _ _ => s top r j

instance : Monad SchemaM := inferInstanceAs (Monad (ExceptT _ _))
instance : Alternative SchemaM where
  failure := throw "failure"
  orElse s f := fun a b c => Except.orElseLazy (s a b c) (fun () => f () a b c)
instance : MonadLift (Except String) SchemaM where
  monadLift e := show ExceptT _ _ _ from liftM e

def toType (_s : SchemaM α) : Type := α
def toType.val {s : SchemaM α} (v : toType s) : α := v

instance {s : SchemaM α} [R : Repr α] : Repr (toType s) := R

instance : CoeSort (SchemaM α) Type where
  coe s := s.toType

instance [I : Inhabited α] {s : SchemaM α} : Inhabited (toType s) := I

end SchemaM

def any : SchemaM Lean.Json := SchemaM.curJson

def ofLeanJson [Lean.FromJson α] : SchemaM α := do
  match Lean.FromJson.fromJson? (← SchemaM.curJson) with
  | .ok a => return a
  | .error e => SchemaM.throw s!
"FromJson error:
{e}

Input JSON:
{(←SchemaM.curJson).pretty}"

/-! Primitive data types -/

def integer : SchemaM Int := ofLeanJson

def number : SchemaM Lean.JsonNumber := ofLeanJson

def string : SchemaM String := ofLeanJson

def boolean : SchemaM Bool := ofLeanJson

/-! Arrays -/

def array (s : SchemaM α) : SchemaM (Array α) := do
  let j ← SchemaM.curJson
  match j with
  | .arr a =>
    let r ← SchemaM.curRef
    a.mapIdxM (fun i j' => SchemaM.withState (r.thenIdx i) j' s)
  | _ => SchemaM.throw s!"expected array, got:\n{j}"

/-! Objects -/

/-- For a given key, if that key exists, specify the schema
    that applies to that key -/
def objectMap {α : String → Type} (f : (s : String) → SchemaM (α s))
    : SchemaM (Lean.RBNode String α) := do
  let j ← SchemaM.curJson
  match j with
  | .obj m =>
    let r ← SchemaM.curRef
    m.mapM (fun k j' => SchemaM.withState (r.thenKey k) j' (f k))
  | _ => SchemaM.throw s!"expected object, got:\n{j}"

private def SchemaM.objField (m : Lean.RBNode String fun _ => Lean.Json) (f : String) (s : SchemaM α) : SchemaM α :=
  do let some next := m.find compare f | SchemaM.throw s!"Required field {f} missing."
     SchemaM.withState ((← SchemaM.curRef).thenKey f) next s

private def SchemaM.objFieldOpt (m : Lean.RBNode String fun _ => Lean.Json) (f : String) (s : SchemaM α)
  : SchemaM (Option α) :=
  match m.find compare f with
  | none => pure none
  | some next => do
    let res ← SchemaM.withState ((← SchemaM.curRef).thenKey f) next s
    return some res

open Lean Elab Deriving Command Lean.Parser.Term Meta in
section

private def withBindersType (b : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) (e : Term) : TermElabM Term :=
  if b.isEmpty then pure e else `(∀ $b:bracketedBinder* , e)

private def withBindersFun (b : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) (e : Term) : TermElabM Term :=
  if b.isEmpty then pure e else `(fun $(b.map (.mk ·.raw)):funBinder* => e)

scoped elab "genStructSchema " defnId:ident "for " struct:ident : command =>
  liftTermElabM do
  let defnId := defnId.getId
  let declName ← resolveGlobalConstNoOverload struct
  let ctx ← mkContext "jsonSchema" declName
  Term.withDeclName defnId <| do
  let header ← mkHeader ``SchemaM 0 ctx.typeInfos[0]!
  let fields := getStructureFieldsFlattened (← getEnv) declName (includeSubobjectFields := false)
  let fieldIdents := fields.map mkIdent
  let mIdent : Ident ← `(m)
  let getters : TSyntaxArray `doElem ← fields.mapM (fun field => do
    let some projFn := getProjFnForField? (← getEnv) (structName := declName) (fieldName := field)
      | throwError "field has no projection function? (bug)"
    let projType ← inferType (← Term.elabTerm (← `($(mkIdent projFn))) none)
    let type := projType.getForallBody
    let (type, optional) :=
      match type.app1? ``Option with
      | some type => (type, true)
      | none => (type, false)
    let some (_type, schema) := type.app2? ``SchemaM.toType
      | throwError "Field {field} has a type which is not derived from a schema:\n{type}
This deriver only works if all fields have a type of the form `SchemaM.toType <schema>`"

    if optional then
      `(doElem| SchemaM.objFieldOpt m $(Syntax.mkStrLit field.toString) $(← schema.toSyntax) )
    else
      `(doElem| SchemaM.objField m $(Syntax.mkStrLit field.toString) $(← schema.toSyntax))
  )
  let type := ← instantiateMVars <| ← Term.elabTerm (expectedType? := none) <|
    ← withBindersType header.binders <| ← `(
      SchemaM $(← mkInductiveApp ctx.typeInfos[0]! header.argNames)
    )
  let value := ← instantiateMVars <| ← Term.elabTerm (expectedType? := some type) <|
    ← withBindersFun header.binders <| ← `(do
    let j ← SchemaM.curJson
    match j with
    | .obj $mIdent =>
      $[let $fieldIdents:ident ← $getters]*
      return { $[$fieldIdents:ident := $(id fieldIdents)],* }
    | _ => SchemaM.throw s!"Expected object ({$(Syntax.mkStrLit declName.toString)}), got:\n{j}")
  addAndCompile (.defnDecl {
    name := defnId
    levelParams := []
    type := type
    hints := default
    safety := .safe
    value := value
  })

end

/-! Subtypes (arbitrary properties on top of a given schema) -/

def SchemaM.withProperty (s : SchemaM α) (errString : α → String) (p : α → Bool)
      : SchemaM { a : α // p a } := do
  let a ← s
  if h : p a then
    return ⟨a,h⟩
  else SchemaM.throw (errString a)

/-! Pairs -/

def guard {β : α → Type} (f : SchemaM α) (g : (a : α) → SchemaM (β a))
      : SchemaM (Σ a, β a) := do
  let a ← f
  let b ← (g a)
  return ⟨a,b⟩

/-! Either -/

def SchemaM.orElse (s1 : SchemaM α) (s2 : SchemaM β) : SchemaM (α ⊕ β) :=
  fun top r j =>
    match s1 top r j with
    | .ok a => .ok (.inl a)
    | .error e1 =>
      match s2 top r j with
      | .ok b => .ok (.inr b)
      | .error e2 =>
        .error s!"multiple failures:\n{e1}\n\n{e2}"

/-! References -/

def reference : SchemaM Reference := do
  let s ← string
  match Reference.fromString s with
  | .ok r => return r
  | .error e =>
    SchemaM.throw s!"reference: failed to parse reference string {s}:\n{e}"

def maybeRefObj (s : SchemaM α) : SchemaM α := do
  match ← SchemaM.curJson with
  | .obj m =>
    match m.find compare "$ref" with
    | none => return ← s
    | some j =>
      if m.size > 1 then
        SchemaM.throw s!"refobj: found $ref key, but it has siblings:\n{← SchemaM.curJson}"

      match j with
      | .str refstr =>
        match Reference.fromString refstr with
        | .error e => SchemaM.throw s!"refobj: found $ref key but failed to parse reference string.\nRefString: {refstr}\nError: {e}"
        | .ok (.pointer p) =>
          match Reference.resolvePointer (← SchemaM.topJson) p with
          | .error e => SchemaM.throw s!"refobj: failed to follow reference path:\n{e}"
          | .ok j =>
          SchemaM.withState (.pointer p) j s
      | _ => s
  | _ => s

/-! SchemaM for core schemas

INCOMPLETE. DO NOT USE.
-/

namespace CoreSchema

inductive «Type»
| protected integer | protected number | protected boolean | protected string
| protected array | protected object
deriving DecidableEq, Lean.ToJson, Lean.FromJson

def Type.toType : «Type» → Type
| .integer => integer
| .number  => number
| .boolean => boolean
| .string  => string
| .array   => array any
| .object  => objectMap fun _ => any

def Type.toJsonSchema (c : «Type») : SchemaM c.toType :=
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
