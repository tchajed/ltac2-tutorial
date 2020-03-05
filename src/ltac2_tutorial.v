(* The first thing to learn is how to import Ltac2. *)
From Ltac2 Require Import Ltac2.

(* If you don't have this, sometimes you'll get a "the following expression
should be of type unit" with no attached expression. *)
Set Warnings "+not-unit".

(* Ltac2 definitions are values, typically functions in the tactic monad that
produce values but potentially constants. Here's a function that's a bit like
Ltac1 [idtac] without the printing support, but note that it is explicitly
thunked. *)
Ltac2 idtac () := ().
(* here's what the above desugars to: *)
Ltac2 idtac' := fun p => match p with
                      | () => ()
                      end.

(*! Variables *)

(* TODO: explain x, @x, &x and $x *)
(* TODO: explain how this used to work in Ltac1 *)

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
Local Ltac2 invc (h: ident) :=
  Std.inversion Std.FullInversion (Std.ElimOnIdent h) None None;
  Std.subst_all ();
  Std.clear [h].

(* here are tons of wrong ways *)
Local Ltac2 invc' (h: ident) :=
  (* this seems right, but it does inversion on a constr whose value is the
  hypothesis, generating a new copy (the original is cleared by clear $h) *)
  let h' := Control.hyp h in
  (* we can't do $h because that's an ident and we're going to pass a constr
  here *)
  inversion $h'; subst; clear $h.

Local Ltac2 invc_bad2 (h: ident) :=
  (* h is parsed as an ident, it's not a variable *)
  inversion h; subst; Std.clear [h].

Local Ltac2 invc_bad1 (h: ident) :=
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
dynamically-typed values of type Ltac1.t. These can be run as tactics or
converted to/from constrs and lists (note that this means Ltac1 ints, strings,
and idents cannot be used - this is probably just an oversight in the API). *)

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
primitives, and concatenation. This also tells us that there's no printf.
 *)

(* Now let's try something harder. Let's solve
https://github.com/coq/coq/issues/11641 - namely, let's implement [Ltac2 change (a:constr) (b:constr)].

First let's figure out where [change] is exposed in Ltac2 - we expect to find a
primitive Ltac2 tactic and an Ltac2 notation. The notation is in [Notations.v],
and it ultimately calls [Std.change].

Here's the definition of change (for its type signature):

[Ltac2 @ external change : pattern option -> (constr array -> constr) -> clause ->
unit := "ltac2" "tac_change".]

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
