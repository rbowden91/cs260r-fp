(*
 * This is not in the Coq library, as far as I can tell.
 *
 * Some of this (without the typeclassery) was taken from
 * https://pdp7.org/blog/2011/01/the-maybe-monad-in-coq/
 *)

Class Monad (M : Type -> Type): Type := {
   ret {a : Type}: a -> M a;
   bind {a b : Type}: M a -> (a -> M b) -> M b;

   left_id: forall (a b : Type), forall (x : a) (f : a -> M b),
      bind (ret x) f = f x;
   right_id {a: Type}: forall (m : M a),
      bind m (fun (x : a) => ret x) = m;
   assoc {a b c: Type}: forall (m : M a) (n: a -> M b) (o : b -> M c),
      bind (bind m n) o = bind m (fun x => bind (n x) o);
}.
 
Notation "M >>= N" := (bind M N)
	(at level 42, left associativity).

Notation "'do' X <- M ; N" := (bind M (fun X => N))
	(at level 200, X ident, M at level 100, N at level 200).

Notation "'do' M ; N" := (bind M (fun _ => N))
	(at level 200, M at level 100, N at level 200).

Instance option_is_monad: Monad option := {
   (* It isn't clear to me why the implicit args need to be explicit. *)
   ret a x := Some x;
   bind a b ma fmb := match ma with
   | Some x => fmb x
   | None => None
   end;
}.
Proof.
   - intros. auto.
   - intros. destruct m; auto.
   - intros. destruct m; auto.
Qed.
