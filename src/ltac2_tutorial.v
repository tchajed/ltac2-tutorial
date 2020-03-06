(*** An Ltac2 tutorial *)

(* You could also ahead and read the refman Ltac2 reference:
https://coq.github.io/doc/master/refman/proof-engine/ltac2.html. It's good to
just get a sense of the features and some of the terminology. However, it will
not teach you Ltac2, hence this guide. *)

(* This tutorial aims to be pragmatic, but it is not specific to an application.
The pragmatics of Ltac2 are likely to change, as the language becomes more
usable. Picking an application and really trying to use Ltac2 for it is likely
to uncover more tricks and bug reports necessary to make the language work. *)

(* The first thing to learn is how to import Ltac2. This was recently added to
the reference manual. *)
From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.

(* The act of importing Ltac2 loads the plugin and makes Ltac2 the default
language for new proofs.

In 8.11.0 loading Ltac2 triggered several bugs, which should be fixed in
8.11.1. *)

(* Ltac2 definitions are values, typically functions in the tactic monad that
produce values but potentially constants. Here's a function that's a bit like
Ltac1 [idtac] without the printing support, but note that it is explicitly
thunked.

This was the first example I wrote, but note that it isn't actually useful - you
should just use () where you absolutely needed idtac in Ltac1 (eg, in a match
pattern that should do nothing). *)
Ltac2 idtac () := ().
(* here's what the above desugars to: *)
Ltac2 idtac' := fun p => match p with
                         | () => ()
                         end.

(*! Hello world *)

(* We can print things in Ltac2, using tools from the Message library. *)

Ltac2 hello_world () := Message.print (Message.of_string "Hello, world!").

Goal True.
  hello_world ().
Abort.

(* We can also evaluate Ltac2 expressions: *)

Ltac2 Eval hello_world ().

(*! Variables *)

(* Ltac2 requires much more precise notation to access variables from
the various contexts - there are Ltac2 variables, Gallina references, and the
dynamic goal environment, for example. *)

(* These notations are generally instances of a more general antiquotation
feature for accessing various sub-languages, including for creating constrs,
idents, and patterns, for example. *)

(* There are four ways to reference a variable:
  - x refers to an Ltac2 variable as-is, within another Ltac2 expression.
  - @x is the same as ident:(x) - it produces an ident for "x"
  - &x is used to refer to a dynamic name. Think of it as x, but it resolves the
    name entirely dynamically. It has two definitions:
     - as an Ltac2 expression, it means [Control.hyp @x], referring to the
       name "x" in the dynamic environment. Note this isn't the same as
       Control.hyp x, which looks up an Ltac2 variable x of type ident.
     - in a constr, it expands to [ltac2:(Control.refine (fun () =>
       Control.hyp @x))]. This is more-or-less the same as the above, but has to
       escape to Ltac2 and back to actually do the lookup.
  - $x refers to an Ltac2 variable x of type constr within a constr:(...)
    antiquotation. It is equivalent to [ltac2:(Control.refine (fun () => x))].
    This is more necessary than it would seem since sometimes an Ltac2 notation
    accepts a constr, so inserting a variable requires this escape.

  I constantly get these mixed up.
 *)

(* Where did all of this complexity come from? In Ltac1, it was actually worse -
there were dynamic heuristics to decide whether something was an Ltac1 variable
or a Gallina identifier, for example. *)

(* Here's an illustration of this: *)
Inductive boole := fact | lie.

(* this doesn't do what it looks like - the fact argument to exact is a constr,
and the boole constructor gets "internalized" (internalization is static
compilation, evaluation is dynamic), while the fact Ltac2-level argument is unused. *)
Ltac2 solve_with := fun fact => exact fact.
Print Ltac2 solve_with. (* note type is 'a -> unit *)

(* we need to use $ to refer to the fact argument *)
Ltac2 solve_with_correct := fun (fact:constr) => exact $fact.
Goal True.
  (* to pass [I] as a constr, we use ', which is a shorthand for the open_constr
  antiquotation (we could have written [constr:(I)], but that's longer). *)
  solve_with_correct 'I.
Qed.

(* In Ltac1 you may get either the bound variable or the global reference. Here,
you get the variable: *)
Ltac solve_with := fun fact => exact fact.
Goal True.
  ltac1:(solve_with I).
Qed.

(* What if we wanted to refer to the global fact of type boole? This still
doesn't work (it still solves the goal using the argument): *)
Ltac solve_with_fact := fun fact => let x := constr:(fact) in exact x.
Goal boole.
  Fail ltac1:(solve_with_fact true).
Abort.

(*! Pretyping *)

(* When you use an ltac2-in-term for a notation (note: this is my made-up
terminology, the refman roughly says "when an Ltac2 antiquotation appears inside
a Coq term notation"), then notation variables are bound to Ltac2 variables of
type preterm. Basically you have to pretype them into constrs, but we can modify
the environment before doing so: *)

(* this the identity, where we just pretype the input and return it (by
solving the antiquotation goal) *)
Notation fancy_identity x := ltac2:(let x := Constr.pretype x in exact $x) (only parsing).
(* Now we're going to do something crazy: pretype the preterm with y bound: *)
Notation with_y x :=
  ltac2:(Control.refine
           (fun _ =>
              constr:(fun (y:nat) =>
                        ltac2:(Control.refine
                                 (fun _ => Constr.pretype x))))) (only parsing).
(* sadly this doesn't work *)
Fail Definition foo := with_y y.

(* ...but this does *)
Definition foo := with_y ltac2:(let x := &y in exact $x).
Print foo.

(* ...and even this *)
Notation get_y := ltac2:(let y := &y in exact $y) (only parsing).
Definition foo' := with_y get_y.
Example foo'_is : foo' = fun (y: nat) => y
  := eq_refl.

Definition foo'' := with_y (get_y + 1).
Example foo''_is : foo'' = fun y => y + 1
  := eq_refl.

(*! Goal and constr matching *)

Ltac2 show_type () :=
  (* this is desugared into something more primitive from Pattern *)
  match! goal with
  | [ |- forall _ : ?e, _ ] =>
    (* There's no dynamically-typed idtac; instead, messages have to be built up
    from simpler forms. There's also no printf, which is annoying because it's
    impossible to write it in a type-safe way in Ltac2's ML type system. *)
    Message.print (Message.of_constr e)
  end.

Goal forall (n:nat), n = n.
Proof.
  show_type ().
Abort.

Theorem test2 (n:nat) (H: 3 < n) (m:nat) : 2 < m.
Proof.
  match! goal with
  (* we really do have to use lowercase for this pattern variable *)
  | [ h: ?t |- _ ] =>
    Message.print (Message.of_ident h)
  end.
  match! goal with
  | [ h: ?t |- _ ] =>
    match! (Constr.type t) with
    | Prop => Message.print (Message.concat (Message.of_ident h)
                                        (Message.concat (Message.of_string " : ")
                                                        (Message.of_constr t)))
    (* backtracking is now via this particular exception (we don't need it here,
     since match! will implicitly insert it as a fallback) *)
    | _ => Control.zero Match_failure
    end
  end.
  match! goal with
  | [ h: ?t |- _ ] =>
    match! (Constr.type t) with
      (* annoyingly [clear h] is an Ltac2 notation where h is parsed as an
      identifier, so it attempts to clear literally h. We can use the
      lower-level API to get what we want, but now for generality it takes an
      array of idents. *)
      (* here that's fine, but in general it can be quite nasty (due to how
      bad the primitive ML tactics are, arguably not the fault of Ltac2) *)
    | Prop => Std.clear [h]
    (* backtracking is now via this particular exception (we don't need it here,
     since match! will implicitly insert it as a fallback) *)
    | _ => Control.zero Match_failure
    end
  end.
Abort.

(*! Standard library tactics *)

(* Ltac1 ML tactics are generally exported as an Ltac2 tactic, then wrapped in
an Ltac2 notation for rough compatibility. Unfortunately these notations aren't
great for use in tactics, since they parse their arguments the wrong way to pass
variables. *)

(* inversion is complicated in general, and we have to figure out what the
simple usage about corresponds to *)
Ltac invc H := inversion H; subst; clear H.
Ltac2 invc (h: ident) :=
  Std.inversion Std.FullInversion (Std.ElimOnIdent h) None None;
  Std.subst_all ();
  Std.clear [h].

(* here are tons of wrong ways *)
Ltac2 invc' (h: ident) :=
  (* this seems right, but it does inversion on a constr whose value is the
  hypothesis, generating a new copy (the original is cleared by clear $h) *)
  let h' := Control.hyp h in
  (* we can't do $h because that's an ident and we're going to pass a constr
  here *)
  inversion $h'; subst; clear $h.

Ltac2 invc_bad2 (h: ident) :=
  (* h is parsed as an ident, it's not a variable *)
  inversion h; subst; Std.clear [h].

Ltac2 invc_bad1 (h: ident) :=
  (* we're asking for literally the name h, in a convoluted way (we're getting Control.hyp @h) *)
  inversion &h; subst; Std.clear [h].

Theorem test2 (n m: nat) (H:Some n = Some m): n = m.
Proof.
  (* we need to call the tactic on an ident (we could wrap it in a notation that
  parses the argument as an identifer by default) *)
  invc @H.
  reflexivity.
Qed.

Theorem test3 (n m: nat) (H:Some n = Some m): n = m.
Proof.
  invc' @H.
  (* this didn't exactly work, since it created a new H0 *)
Abort.

(*! Calling Ltac1 from Ltac2 *)

(* this is really easy in a script - just do ltac1:(...) *)

Ltac foo := ltac2:(1).
(* Without this, in the above you get a warning "The following expression should
have type unit." with no attached location. We should report this as a bug -
this message is useless as a warning. *)
Set Warnings "+not-unit".

Fail Ltac foo' := ltac2:(Std.change).

(* wrapping functions is possible but a bit obscure, because we have to take the
arguments in Ltac2 and pass them as dynamic values to Ltac1. *)
Local Ltac2 replace_with (lhs: constr) (rhs: constr) :=
  ltac1:(lhs rhs |- replace lhs with rhs)
          (Ltac1.of_constr lhs) (Ltac1.of_constr rhs).
Ltac2 Notation "replace" lhs(constr) "with" rhs(constr) :=
  replace_with lhs rhs.

(*! Calling Ltac2 from Ltac1 *)

(* The FFI to call into Ltac2 is to call an Ltac2 expression of type unit that
solves a goal. There is a mechanism to pass arguments, which are represented as
dynamically-typed values of type Ltac1.t (this is just the reverse of the
above). These can be run as tactics or converted to/from constrs and lists (note
that this means Ltac1 ints and strings cannot be used - this is probably just an
oversight in the API). *)

Ltac2 add1 (n:constr) := constr:(1 + $n).
Ltac add1 :=
  ltac2:(n |- let n := Option.get (Ltac1.to_constr n) in
              let n_plus_1 := add1 n in
              exact $n_plus_1).

(*! Datatypes in Ltac2 *)

(* you can create new datatypes in Ltac2 *)
Ltac2 Type ABC := [A | B(bool) | C(constr)].

Ltac2 Notation x(self) "++" y(self) := Message.concat x y.

(* you can annotate input types but not return types (this is an oversight and
should be fixed); without annotations you get Hindley-Milner, inluding
polymorphism *)
Ltac2 msg_of_bool (b: bool) := Message.of_string
                                 (match b with
                                  | true => "true"
                                  | false => "false"
                                  end).

(* explain_abc : ABC -> unit *)
Ltac2 explain_abc abc :=
  match abc with
  | A => Message.print (Message.of_string "A")
  | B b => Message.print (Message.of_string "B " ++ msg_of_bool b)
  | C c => Message.print (Message.of_string "C " ++ Message.of_constr c)
  end.

Print Ltac2 explain_abc.

(*! Exceptions *)

(* Ltac2 has good support for exceptions. The support is based on the [exn]
_open type_, which supports dynamic extension and thus eliminating exn always
requires a catch-all case. You can create your own open types in Ltac2, but
let's focus on this one. *)

Ltac2 Type exn ::= [ MyNewException(string) ].

(* the simplest thing we can do with the new exception is to panic/throw it,
which is unrecoverable *)

Goal True.
  Fail Control.throw (MyNewException ("oops")).
  (*  Uncaught Ltac2 exception: MyNewException ("oops") *)
Abort.

(* Ltac2 also has first-class backtracking via exceptions *)

(* The refman explains this support as "viewing thunks as lazy lists", and then
the zero and plus operators are the empty list and concatenation operators, and
also these are a monoid. I don't really understand this, but here's an example
of a "backtracking string" and how you can view it as a list of two strings: *)

Ltac2 x_or_y () := Control.plus (fun () => "x") (fun _ => "y").

Ltac2 get_x_and_y () :=
  match Control.case x_or_y with
  | Val xyf => let (x, yf) := xyf in
               (x, yf Not_found)
  | Err exn => Control.throw exn
end.

Ltac2 Eval get_x_and_y ().

(* I think this is really powerful? *)

(* One limitation I can see is that exceptions aren't typed: there's a single
dynamic type with all the exceptions, and all Ltac2 code is in a single effect,
one with exceptions and a proofview. *)

(*! Reading the Ltac2 source *)

(* You will need to read the Ltac2 source
(https://github.com/coq/coq/tree/master/user-contrib/Ltac2) to figure out how
things work. This ranges from fine to totally impossible.

For example, let's figure out the Message API. We open
https://github.com/coq/coq/blob/master/user-contrib/Ltac2/Message.v and look at
what's there. It doesn't have a type [Message.t] but just [message], so find
it's definition - it's defined as [Ltac2 Type message], which means it comes
from OCaml. That's fine, it's opaque anyway.

In Message.v we see one eliminator (print), a few constructors for Ltac2
primitives, and concatenation. This also tells us that there's no printf. *)

(* Now let's try something harder. Let's solve
https://github.com/coq/coq/issues/11641 - namely, let's implement [Ltac2 change
(a:constr) (b:constr)].

First let's figure out where [change] is exposed in Ltac2 - we expect to find a
primitive Ltac2 tactic and an Ltac2 notation. The notation is in [Notations.v],
and it ultimately calls [Std.change].

Here's the definition of change (for its type signature):

[Ltac2 @ external change : pattern option -> (constr array -> constr) -> clause
-> unit := "ltac2" "tac_change".]

This takes a pattern option for the thing to change, a (constr array -> constr)
for the right-hand side (the argument is stuff bound by the pattern), and an
occurrence clause for where to apply the change (a subset of the goals and
hypotheses). *)

(* First-class occurrence clauses are really nice in Ltac2, but only
if you use the tactics and not the notations. Anyway for now we're going to
ignore the clause and just set it to the goal. (we can look at the definition of
clause to see how to write that) *)
Ltac2 goal_clause := {Std.on_hyps := None; Std.on_concl := Std.AllOccurrences}.

(* First, the pattern stuff. First we learn that [change] actually takes
patterns as arguments: *)
Goal 2 + 3 = 5.
Proof.
  change (?x + ?y) with ($y + $x).
  (* in Ltac1 we don't antiquote to refer to bound variables, they're resolved
  dynamically *)
  ltac1:(change (?x + ?y) with (y + x)).
Abort.

(* Now that we're edified we want to forget about patterns and just pass a
constr, and ignore the [constr array] argument for the right-hand side of the
change. This is the hard part. *)

(* We learn from @ppedrot's answer that pattern:(...) is the right way to
construct a pattern... but there's the only way to convert a constr to a pattern
is the OCaml pattern_of_constr function, which is "broken" and thus will not be
exposed to Ltac2. *)

(* The astute reader will observe that we are stuck at this point. It's still
possible to pass the constr to Ltac1 and do the change that way (using
[pattern_of_constr] implicitly), but there's no pure Ltac2 solution.

Instead, we really need to open an issue asking for a variant of [change] that
operates on constrs rather than patterns (@ppedrot calls this a variant of [set]
that does a conversion rather than posing a variable, but that explanation seems
convoluted to me). *)
