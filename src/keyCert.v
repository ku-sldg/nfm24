
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Import ListNotations.

Class DecEq (A : Type) := 
{
  decEq : forall x1 x2 : A, {x1 = x2} + {x1 <> x2}
}.

Ltac fdeq :=
  eauto; intros HC; inversion HC; congruence.

Ltac ddeq :=
  econstructor;
  match goal with
  | |- forall x1 x2 : _,_ =>
      destruct x1, x2; eauto;
      try right; fdeq
  end.

Ltac ideq :=
  econstructor;
  match goal with
  | |- forall x1 x2 : _,_ =>
      induction x1 as [|x1 IHx1]; destruct x2;
      try destruct (IHx1 x2); eauto
  end.





(* TPM Keys *)
(* ******** *)


(* Each key pair has a unique identifier *)
Definition keyIdType := nat.


(* TPM key attributes relevant to this specification *)

Inductive Restricted : Type :=
| Restricting
| NonRestricting.

Inductive Sign : Type :=
| Signing
| NonSigning.

Inductive Decrypt : Type :=
| Decrypting
| NonDecrypting.

(* The FixedTPM attribute is assumed to always be set *)


(* Key pair definitions *)

Inductive pubKey : Type :=
| Public : keyIdType -> Restricted -> Sign -> Decrypt -> pubKey.

Inductive privKey : Type :=
| Private : keyIdType -> Restricted -> Sign -> Decrypt -> privKey.


(* Functions to get a key's inverse *)

Definition pubToPrivKey (k : pubKey) : privKey :=
  match k with
  | Public i r s d => Private i r s d
  end.

Definition privToPubKey (k : privKey) : pubKey :=
  match k with
  | Private i r s d => Public i r s d
  end.


(* Attribute requirements for EK, AK, DevID, and CA keys *)

Definition endorsementKey (k : pubKey) : Prop :=
  match k with
  | Public _ Restricting NonSigning Decrypting => True
  | _ => False
  end.

Definition attestationKey (k : pubKey) : Prop :=
  match k with
  | Public _ Restricting Signing NonDecrypting => True
  | _ => False
  end.

Definition devidKey (k : pubKey) : Prop :=
  match k with
  | Public _ NonRestricting Signing NonDecrypting => True
  | _ => False
  end.

Definition caKey (k : pubKey) : Prop :=
  match k with
  | Public _ NonRestricting Signing NonDecrypting => True
  | _ => False
  end.


(* Decidable equality of keys *)
Local Instance decEq_keyID : DecEq keyIdType.
  ideq.
Qed.

Local Instance decEq_Restricted : DecEq Restricted.
  ddeq.
Qed.
  
Local Instance decEq_Sign : DecEq Sign.
  ddeq.
Qed.

Local Instance decEq_Decrypt : DecEq Decrypt.
  ddeq.
Qed.

Local Instance decEq_pubKey : DecEq pubKey.
  econstructor; induction x1; destruct x2;
  destruct (decEq k k0);
  destruct (decEq r r0);
  destruct (decEq s s0);
  destruct (decEq d d0);
  subst; eauto; right; fdeq.
Qed.

Local Instance decEq_privKey : DecEq privKey.
  econstructor; induction x1; destruct x2.
  destruct (decEq k k0); 
  destruct (decEq r r0);
  destruct (decEq s s0); 
  destruct (decEq d d0);
  subst; eauto; right; fdeq.
Qed.






















(* Messages *)
(* ******** *)


(* Arbitrary type to model identifying information *)
Definition tpmInfoType := nat.
Definition deviceInfoType := nat.

Inductive identifier : Type :=
| TPM_info : tpmInfoType -> identifier
| Device_info : deviceInfoType -> identifier.


Inductive signedCert : Type :=
| Cert : pubKey -> identifier -> privKey -> signedCert.


(* Arbitrary type to model random numbers *)
Definition randType := nat.


(* Messages includes all structures required in this specification *)
Inductive message : Type :=
| publicKey : pubKey -> message
| privateKey : privKey -> message
| hash : message -> message
| signature : message -> privKey -> message
| TPM2B_Attest : pubKey -> message
| encryptedCredential : message -> randType -> pubKey -> message
| randomNum : randType -> message
| TCG_CSR_IDevID : identifier -> signedCert -> pubKey -> message
| TCG_CSR_LDevID : message -> signedCert -> message
| signedCertificate : signedCert -> message
| pair : message -> message -> message.


(* Decidable equality of messages *)

Local Instance decEq_identifier : DecEq identifier.
  econstructor; induction x1; destruct x2; try (right; fdeq);
  try destruct (decEq t t0);
  try destruct (decEq d d0);
  subst; eauto; right; fdeq.
Qed.

Local Instance decEq_signedCert : DecEq signedCert.
  econstructor; destruct x1, x2;
  destruct (decEq p p1); 
  destruct (decEq i i0); 
  destruct (decEq p0 p2);
  subst; eauto; right; fdeq.
Qed.

Local Instance decEq_randType : DecEq randType.
  ideq.
Qed.

Local Instance decEq_message : DecEq message.
  econstructor; induction x1; destruct x2; try (right; fdeq);
  try destruct (decEq p p0);
  try destruct (decEq r r0);
  try destruct (decEq i i0);
  try destruct (decEq s s0);
  try destruct (IHx1 x2);
  subst; eauto; try (right; fdeq).
  destruct (IHx1_1 x2_1);
  destruct (IHx1_2 x2_2);
  subst; eauto; right; fdeq.
Qed.












(* Commands *)
(* ******** *)


(* Includes both TPM and non-TPM commands required in this specification *)
Inductive command : Type :=
| CheckAttributes : pubKey -> Restricted -> Sign -> Decrypt -> command
| TPM2_Hash : message -> command
| CheckHash : message -> message -> command
| TPM2_Sign : message -> privKey -> command
| TPM2_Certify : pubKey -> privKey -> command
| CheckSig : message -> pubKey -> command
| MakeCSR_IDevID : identifier -> signedCert -> pubKey -> command
| MakeCSR_LDevID : message -> signedCert -> command
| CheckCert : signedCert -> pubKey -> command
| MakePair : message -> message -> command
| TPM2_ActivateCredential : message -> privKey -> privKey -> command.
(* | CheckRandom : message -> randType -> command *)


(* State corresponds to what an entity knows *)
(* States are treated as sets *)

Definition state := list message.

(* TPM State contains everything produced by a TPM command *)
(* Subset of the general state *)
Definition tpm_state := list message.


(* Set inclusion over states *)

Definition Included (st1 st2 : list message) : Prop := forall m,
In m st1 ->
In m st2.

Notation "st1 \subsetOf st2" := (Included st1 st2) (at level 92, left associativity).

Lemma Included_transitive : forall st1 st2 st3,
  st1 \subsetOf st2 ->
  st2 \subsetOf st3 ->
  st1 \subsetOf st3.
Proof.
  intros st1 st2 st3 H12 H23; intros m' I; 
  apply H23; apply H12; assumption.
Qed.




(* Decidable equality of commands *)
Local Instance decEq_command : DecEq command.
  econstructor; induction x1; destruct x2; try (right; fdeq);
  try destruct (decEq p p0);
  try destruct (decEq r r0);
  try destruct (decEq s s0);
  try destruct (decEq d d0);
  try destruct (decEq m m0);
  try destruct (decEq i i0);
  try (destruct (decEq m m1); destruct (decEq m0 m2));
  try (destruct (decEq p p1); destruct (decEq p0 p2));
  subst; eauto; right; fdeq.
Qed.







(* Execution of Commands *)
(* ********************* *)


(* Inductive proposition describing individual command execution *)
(* Relates an initial state, a command, and a final state *)
  Inductive execute : tpm_state * state -> command -> tpm_state * state -> Prop :=
(*
  CheckAttributes
  ***************
  Inputs: 
    Public Key
    Attributes
  Success Conditions:
    Public Key is in state
    Public Key has all Attributes
  Updates to State:
    None
*)
| E_CheckAttributes : forall stTPM st i r s d,
    In (publicKey (Public i r s d)) st ->
    execute (stTPM, st)
            (CheckAttributes (Public i r s d) r s d)
            (stTPM,
             st)
(*
  TPM2_Hash
  *********
  Inputs: 
    Message
  Success Conditions:
    None
  Updates to State:
    The hash of Message to TPM State
*)
| E_Hash : forall stTPM st m,
    In m st ->
    execute (stTPM, st)
            (TPM2_Hash m)
            (hash m :: stTPM,
             hash m :: st)
(*
  CheckHash
  *********
  Inputs: 
    Hash
    Message
  Success Conditions:
    Hash is in state
    Message is in state
    Hash is the hash of Message
  Updates to State:
    None
*)
| E_CheckHash : forall stTPM st m,
    In (hash m) st ->
    In m st ->
    execute (stTPM, st)
            (CheckHash (hash m) m)
            (stTPM,
             st)
(*
  TPM2_Sign Restricted
  ********************
  Inputs: 
    Message
    Private Key
  Success Conditions:
    Private Key resides in TPM
    Message resides in TPM
    Private Key has Restricting and Signing attributes
  Updates to State:
    Message signed by Private Key to TPM State
*)
| E_SignR : forall stTPM st m i d,
    In (privateKey (Private i Restricting Signing d)) stTPM ->
    In m stTPM ->
    execute (stTPM,st)
            (TPM2_Sign m (Private i Restricting Signing d))
            (signature m (Private i Restricting Signing d) :: stTPM,
             signature m (Private i Restricting Signing d) :: st)
(*
  TPM2_Sign Not-Restricted
  ************************
  Inputs: 
    Message
    Private Key
  Success Conditions:
    Private Key resides in TPM
    Message is in state
    Private Key has NonRestricting and Signing attributes
  Updates to State:
    Message signed by Private Key to TPM State
*)
| E_SignNR : forall stTPM st m i d,
    In (privateKey (Private i NonRestricting Signing d)) stTPM ->
    In m st ->
    execute (stTPM, st)
            (TPM2_Sign m (Private i NonRestricting Signing d))
            (signature m (Private i NonRestricting Signing d) :: stTPM,
             signature m (Private i NonRestricting Signing d) :: st)
(*
  CheckSig
  ********
  Inputs: 
    Signature
    Public Key
  Success Conditions:
    Signature is in state
    Public Key is in state
    Public Key is the inverse of the key that created Signature
  Updates to State:
    None
*)
| E_CheckSig : forall stTPM st m i r s d,
    In (signature m (Private i r s d)) st ->
    In (publicKey (Public i r s d)) st ->
    execute (stTPM, st)
            (CheckSig (signature m (Private i r s d)) (Public i r s d))
            (stTPM,
             st)
(*
  TPM2_Certify
  ************
  Inputs: 
    Public Key
    Private Key
  Success Conditions:
    Public Key is in state
    The inverse of Public Key resides in TPM
    Private Key resides in TPM
    Private Key has Signing attribute
  Updates to State:
    TPM2B_Attest structure of Public Key signed by Private Key to TPM State
*)
| E_Certify : forall stTPM st i r s d i0 r0 d0,
    (*In (publicKey (Public i r s d)) st ->*)
    In (privateKey (Private i r s d)) stTPM -> 
    In (privateKey (Private i0 r0 Signing d0)) stTPM ->
    execute (stTPM, st)
            (TPM2_Certify (Public i r s d) (Private i0 r0 Signing d0))
            (signature (TPM2B_Attest (Public i r s d)) (Private i0 r0 Signing d0) :: stTPM,
             signature (TPM2B_Attest (Public i r s d)) (Private i0 r0 Signing d0) :: st)
(*
  TPM2_ActivateCredential
  ***********************
  Inputs: 
    Encrypted Credential (contains Message and Random Number)
    Private Key A
    Private Key B
  Success Conditions:
    Encrypted Credential is in state
    Private Key A resides in TPM
    Private Key B resides in TPM
    Private Key A is the inverse of the key that created Encrypted Credential
    Message is the hash of the inverse of Private Key B
  Updates to State:
    Random Number to TPM State
*)
| E_ActivateCredential : forall stTPM st n g i r s d i0 r0 s0 d0,
    In (encryptedCredential n g (Public i r s d)) st ->
    In (privateKey (Private i r s d)) stTPM ->
    In (privateKey (Private i0 r0 s0 d0)) stTPM ->
    execute (stTPM, n::st) (CheckHash n (publicKey (Public i0 r0 s0 d0))) (stTPM, n::st) ->
    execute (stTPM, st)
            (TPM2_ActivateCredential (encryptedCredential n g (Public i r s d)) 
                                      (Private i r s d)
                                      (Private i0 r0 s0 d0)) 
            (randomNum g :: stTPM,
             randomNum g :: st)

(*
  CheckRandom
  **********
  Inputs: 
    Random Number
    Golden Value
  Success Conditions:
    Golden Value resides in TPM
    Random Number is Golden Value
  Updates to State:
    None

| E_CheckRandom : forall stTPM st g,
    In (randomNum g) stTPM ->
    execute (stTPM, st)
            (CheckRandom (randomNum g) g)
            (stTPM,
             st)
*)
(*
  MakeCSR_IDevID
  **************
  Inputs: 
    Certificate
    Public Key
  Success Conditions:
    Certificate is in state
    Public Key is in state
  Updates to State:
    TCG_CSR_IDevID of Certificate and Public Key to State
*)
| E_MakeCSR_IDevID : forall stTPM st id crt k,
    In (signedCertificate crt) st ->
    In (publicKey k) st ->
    execute (stTPM, st)
            (MakeCSR_IDevID id crt k)
            (stTPM,
             TCG_CSR_IDevID id crt k :: st)
(*
  MakeCSR_LDevID
  **************
  Inputs: 
    Message
    Certificate
  Success Conditions:
    Message is in state
    Certificate is in state
  Updates to State:
    TCG_CSR_LDevID of Message and Certificate to State
*)
| E_MakeCSR_LDevID : forall stTPM st m crt,
    In m st ->
    In (signedCertificate crt) st ->
    execute (stTPM, st)
            (MakeCSR_LDevID m crt)
            (stTPM,
             TCG_CSR_LDevID m crt :: st)
(*
  CheckCert
  *********
  Inputs: 
    Signed Certificate
    Public Key
  Success Conditions:
    Signed Certificate is in state
    Public Key is in state
    Public Key is the inverse of the key that created Signed Certificate
  Updates to State:
    None
*)
| E_CheckCert : forall stTPM st k id i r s d,
    In (signedCertificate (Cert k id (Private i r s d))) st ->
    In (publicKey (Public i r s d)) st ->
    execute (stTPM, st)
            (CheckCert (Cert k id (Private i r s d)) (Public i r s d))
            (stTPM,
             st)
(*
  MakePair
  ********
  Inputs:
    Message A
    Message B
  Success Conditions:
    Message A is in state
    Message B is in state
  Updates to State:
    Pair of Message A and Message B to state *)
| E_MakePair : forall stTPM st m1 m2,
    In m1 st ->
    In m2 st ->
    execute (stTPM, st)
            (MakePair m1 m2)
            (stTPM,
             pair m1 m2 :: st).


Lemma exec_deterministic : forall ini c fin1 fin2,
  execute ini c fin1 ->
  execute ini c fin2 ->
  fin1 = fin2.
Proof.
  intros ini c fin1 fin2 E1 E2;
  destruct E1; inversion E2; subst; reflexivity.
Qed.

Lemma exec_expansion : forall iniTPM ini c finTPM fin,
  execute (iniTPM,ini) c (finTPM,fin) ->
  (iniTPM \subsetOf finTPM) /\
  (ini \subsetOf fin).
Proof.
  intros iniTPM ini c finTPM fin E; split;
  destruct c; inversion E; subst; 
  intros m' I; try (repeat apply in_cons); assumption.
Qed.

Lemma exec_cannotGenerateKey : forall c iniTPM ini finTPM fin k,
  execute (iniTPM, ini) c (finTPM, fin) ->
  In (privateKey k) finTPM ->
  In (privateKey k) iniTPM.
Proof.
  destruct c; intros iniTPM ini finTPM fin k E I;
  inversion E; subst; try inversion I as [EQ_false | I']; try inversion EQ_false; assumption.
Qed.

(*
Lemma exec_cannotGenerateCred : forall c iniTPM ini finTPM fin n g k,
  execute (iniTPM, ini) c (finTPM, fin) ->
  In (encryptedCredential n g k) fin ->
  In (encryptedCredential n g k) ini.
Proof.
  destruct c; intros iniTPM ini finTPM fin n g k E I;
  inversion E; subst; try inversion I as [EQ_false | I']; try inversion EQ_false; assumption.
Qed.
*)

Lemma exec_cannotGenerateCred_contrapositive : forall c iniTPM ini finTPM fin n g k,
  execute (iniTPM, ini) c (finTPM, fin) ->
  ~ (In (encryptedCredential n g k) ini) ->
  ~ (In (encryptedCredential n g k) fin).
Proof.
  destruct c; intros iniTPM ini finTPM fin n g k E N;
  inversion E; subst; try assumption; intros HC; inversion HC; try inversion H; congruence.
Qed.












(* Execution of Sequences of Commands *)
(* ********************************** *)


Inductive sequence : Type :=
| Sequence : command -> sequence -> sequence
| Done : sequence.

Infix ";;" := Sequence (at level 60, right associativity).


Fixpoint command_in_sequence (seq : sequence) (cmd : command) :=
  match seq with
  | c ;; s =>
      if (decEq cmd c)
      then True
      else command_in_sequence s cmd
  | Done => False
  end.

Inductive seq_execute : tpm_state * state -> sequence -> tpm_state * state -> Prop :=
| SE_Seq : forall ini mid fin c s,
    execute ini c mid ->
    seq_execute mid s fin ->
    seq_execute ini (Sequence c s) fin
| SE_Done : forall ini,
    seq_execute ini Done ini.

(* Sequential execution relation is a partial function *)
Theorem seq_exec_deterministic : forall ini s fin1 fin2,
  seq_execute ini s fin1 ->
  seq_execute ini s fin2 ->
  fin1 = fin2.
Proof.
  intros ini s fin1 fin2 E1 E2; generalize dependent fin2;
  induction E1; intros fin2 E2; inversion E2; subst.
  - assert (mid = mid0) as EQ_mid;
    [ apply exec_deterministic with (ini := ini) (c := c)
    | apply IHE1; rewrite <- EQ_mid in H5 ]; assumption.
  - reflexivity.
Qed.

(* Sequential execution does not remove elements from the state *)
Theorem seq_exec_expansion : forall iniTPM ini s finTPM fin,
  seq_execute (iniTPM,ini) s (finTPM,fin) ->
  (iniTPM \subsetOf finTPM) /\
  (ini \subsetOf fin).
Proof.
  intros iniTPM ini s finTPM fin E; split;
  generalize dependent fin; generalize dependent finTPM;
  generalize dependent ini; generalize dependent iniTPM;
  induction s; intros;
  inversion E; subst; try (intros m' I; assumption);
  destruct mid as [midTPM mid];
  assert (Inc : (iniTPM \subsetOf midTPM) /\ (ini \subsetOf mid)); 
  try (apply exec_expansion with (c := c); assumption).
  - apply Included_transitive with (st2 := midTPM);
    [ apply Inc
    | apply IHs with (ini := mid) (fin := fin); assumption ].
  - apply Included_transitive with (st2 := mid);
    [ apply Inc
    | apply IHs with (iniTPM := midTPM) (finTPM := finTPM); assumption ].
Qed.

(* Sequential execution cannot add a key to the state *)
Theorem seq_exec_cannotGenerateKey : forall s iniTPM ini finTPM fin k,
  seq_execute (iniTPM, ini) s (finTPM, fin) ->
  In (privateKey k) finTPM ->
  In (privateKey k) iniTPM.
Proof.
  induction s; intros iniTPM ini finTPM fin k E I;
  inversion E; subst; try assumption; destruct mid as [midTPM mid];
  eapply exec_cannotGenerateKey; eauto.
Qed.

(*
(* Sequential execution cannot add an encrypted credential to the state *)
Lemma seq_exec_cannotGenerateCred : forall s iniTPM ini finTPM fin n g k,
  seq_execute (iniTPM, ini) s (finTPM, fin) ->
  In (encryptedCredential n g k) fin ->
  In (encryptedCredential n g k) ini.
Proof.
  induction s; intros iniTPM ini finTPM fin n g k E I;
  inversion E; subst; try assumption; destruct mid as [midTPM mid];
  eapply exec_cannotGenerateCred; eauto.
Qed.
*)

Lemma seq_exec_cannotGenerateCred_contrapositive : forall s iniTPM ini finTPM fin n g k,
  seq_execute (iniTPM, ini) s (finTPM, fin) ->
  ~ (In (encryptedCredential n g k) ini) ->
  ~ (In (encryptedCredential n g k) fin).
Proof.
  induction s; intros iniTPM ini finTPM fin n g k E N;
  inversion E; subst; try assumption; destruct mid as [midTPM mid];
  eapply IHs; eauto;
  eapply exec_cannotGenerateCred_contrapositive; eauto.
Qed.

(* Sequenctial execution cannot add a random number to the state without an encrypted credential *)
Lemma seq_exec_cannotGenerateRand_contrapositive : forall s iniTPM ini finTPM fin g,
  seq_execute (iniTPM, ini) s (finTPM, fin) ->
  ~ (In (randomNum g) ini) ->
  (forall n k, ~ In (encryptedCredential n g k) ini) ->
  ~ (In (randomNum g) fin).
Proof.
  induction s; intros iniTPM ini finTPM fin g E Ng N.
  - destruct c; inversion E; inversion H2; 
    subst; eapply IHs; try fdeq;
    try (intros n0 k HC; inversion HC; try congruence; destruct (N n0 k); assumption).
    intros HC; inversion HC;
    [ inversion H; subst; destruct (N n (Public i r s1 d)); assumption
    | congruence ].
  - inversion E; subst; congruence.
Qed.




(* Message Inference *)
(* ***************** *)


Inductive inferrable : message -> state -> Prop :=
| I_publicKey : forall k,
    inferrable (publicKey k)
               [publicKey k]
| I_privateKey : forall k,
    inferrable (privateKey k)
               [privateKey k]
| I_hash : forall m,
    inferrable (hash m)
               [hash m]
| I_signature : forall m k st,
    inferrable m st ->
    inferrable (signature m k)
               (signature m k :: st)
| I_Attest : forall k,
    inferrable (TPM2B_Attest k)
               [TPM2B_Attest k ; publicKey k]
| I_encryptedCredential : forall n g k,
    inferrable (encryptedCredential n g k)
               [encryptedCredential n g k]
| I_randomNum : forall g,
    inferrable (randomNum g)
               [randomNum g]
| I_CSR_IDevID : forall id crt k st,
    inferrable (signedCertificate crt) st ->
    inferrable (TCG_CSR_IDevID id crt k)
               (TCG_CSR_IDevID id crt k :: publicKey k :: st)
| I_CSR_LDevID : forall m crt st1 st2,
    inferrable m st1 ->
    inferrable (signedCertificate crt) st2 ->
    inferrable (TCG_CSR_LDevID m crt) 
               (TCG_CSR_LDevID m crt :: st1 ++ st2)
| I_signedCertificate : forall k id k_ca,
    inferrable (signedCertificate (Cert k id k_ca)) 
               [signedCertificate (Cert k id k_ca) ; publicKey k]
| I_pair : forall m1 m2 st1 st2,
    inferrable m1 st1 ->
    inferrable m2 st2 -> 
    inferrable (pair m1 m2) 
               (pair m1 m2 :: st1 ++ st2).

Fixpoint inferFrom (msg : message) : state :=
match msg with
  | signature m k => 
      (signature m k :: inferFrom m)
  | TPM2B_Attest k => 
      [TPM2B_Attest k ; publicKey k]
  | TCG_CSR_IDevID id0 (Cert k id k_ca) k0 => 
      [TCG_CSR_IDevID id0 (Cert k id k_ca) k0 ; publicKey k0 ; signedCertificate (Cert k id k_ca) ; publicKey k]
  | TCG_CSR_LDevID m (Cert k id k_ca) => 
      (TCG_CSR_LDevID m (Cert k id k_ca) :: inferFrom m ++ [signedCertificate (Cert k id k_ca) ; publicKey k])
  | signedCertificate (Cert k id k_ca) => 
      [signedCertificate (Cert k id k_ca) ; publicKey k]
  | pair m1 m2 => 
      (pair m1 m2 :: inferFrom m1 ++ inferFrom m2)
  | _ => 
      [msg]
end.

(* inferFrom function and inferrable relation are equivalent *)
Lemma inferFrom_iff_inferrable : forall m st,
  inferFrom m = st <-> inferrable m st.
Proof.
  intros m st; split; intros H.
  - generalize dependent m; assert (HI : forall m, inferrable m (inferFrom m)); intros m.
  -- induction m; simpl; try destruct c; try destruct s; 
     repeat constructor; assumption.
  -- intros H; induction m; subst; apply HI.
  - induction H; simpl; subst; try destruct crt; reflexivity.
Qed.


Fixpoint inferFromState (st : state) : state :=
  match st with
  | m :: st' => inferFrom m ++ inferFromState st'
  | _ => st
  end.
  













(* *************************** *)
(* Key Certification Protocols *)
(* *************************** *)
(* *************************** *)




(* Only keys and certificates may reside in the initial states
   of Owner and OEM *)
Definition needsGenerated (m : message) : Prop :=
  match m with
  | hash _ => True
  | signature _ _ => True
  | TPM2B_Attest _ => True
  | encryptedCredential _ _ _ => True
  | randomNum _ => True
  | TCG_CSR_IDevID _ _ _ => True
  | TCG_CSR_LDevID _ _ => True
  | pair _ _ => True
  | _ => False
  end.


  Definition lower_bound seq minTPM min : Prop :=
    forall iniTPM ini fin,
    seq_execute (iniTPM, ini) seq fin ->
    (minTPM \subsetOf iniTPM) /\ (min \subsetOf ini).

  Definition sufficient seq minTPM min : Prop :=
    exists fin, seq_execute (minTPM, min) seq fin.








(* Owner/Admin creation of LAK certificate based on IAK certificate *)
(* **************************************************************** *)


(* Supersequence intermediate definitions and lemmas *)

(*
... ;; MakePair csr sig ;; ...
*)
Fixpoint containsStep5_Owner (seq : sequence) (csr sig : message) : Prop :=
  match seq with
  | c ;; s =>
      match c with
      | MakePair m1 m2 =>
          if (decEq csr m1)
          then (
            if (decEq sig m2)
            then True (* Done *)
            else containsStep5_Owner s csr sig )
          else containsStep5_Owner s csr sig
      | _ => containsStep5_Owner s csr sig
      end
  | Done => False
  end.

Lemma containsStep5_Owner_lemma : forall s iniTPM ini finTPM fin csr sig,
  seq_execute (iniTPM, ini) s (finTPM, fin) ->
  In (pair csr sig) fin ->
  ~ (In (pair csr sig) ini) ->
  containsStep5_Owner s csr sig.
Proof.
  induction s; intros iniTPM ini finTPM fin csr sig E I N0.
  - destruct c; simpl in *; inversion E; inversion H2; 
    subst; try (eapply IHs; fdeq);
    destruct (decEq csr m);
    destruct (decEq sig m0);
    subst; trivial;
    eapply IHs; fdeq.
  - inversion E; subst; congruence.
Qed.


(*
... ;; TPM2_Sign hsh (pubToPrivKey lak) ;; 
... ;; MakePair csr (signature hsh (pubToPrivKey lak)) ;; ...
*)
Fixpoint containsSteps4to5_Owner (seq : sequence) (hsh csr : message) (lak : pubKey) : Prop :=
  match seq with
  | c ;; s =>
      match c with
      | TPM2_Sign m k =>
          if (decEq hsh m)
          then (
            if (decEq (pubToPrivKey lak) k)
            then containsStep5_Owner s csr (signature hsh (pubToPrivKey lak))  (* Find next *)
            else containsSteps4to5_Owner s hsh csr lak )
          else containsSteps4to5_Owner s hsh csr lak
      | _ => containsSteps4to5_Owner s hsh csr lak
      end
  | Done => False
  end.

Lemma containsSteps4to5_Owner_lemma : forall s iniTPM ini finTPM fin hsh csr lak,
  seq_execute (iniTPM, ini) s (finTPM, fin) ->
  In (pair csr (signature hsh (pubToPrivKey lak))) fin ->
  ~ (In (pair csr (signature hsh (pubToPrivKey lak))) ini) ->
  ~ (In (signature hsh (pubToPrivKey lak)) ini) ->
  (forall k, hsh <> TPM2B_Attest k) ->
  containsSteps4to5_Owner s hsh csr lak.
Proof.
  induction s; intros iniTPM ini finTPM fin hsh csr lak E I N0 N1 NA.
  - destruct c; simpl in *; inversion E; inversion H2; 
    subst; try (eapply IHs; fdeq);
    destruct (decEq hsh m);
    try destruct (decEq (pubToPrivKey lak) (Private i Restricting Signing d));
    try destruct (decEq (pubToPrivKey lak) (Private i NonRestricting Signing d));
    subst; try eapply IHs; try eapply containsStep5_Owner_lemma; fdeq.
  - inversion E; subst; congruence.
Qed.


(*
... ;; TPM2_Hash csr ;;
... ;; TPM2_Sign (hash csr) (pubToPrivKey lak) ;;
... ;; MakePair csr (signature (hash csr) (pubToPrivKey lak)) ;; ...
*)
Fixpoint containsSteps3to5_Owner (seq : sequence) (csr : message) (lak : pubKey) : Prop :=
  match seq with
  | c ;; s => 
      match c with 
      | TPM2_Hash m => 
          if (decEq csr m)
          then containsSteps4to5_Owner s (hash m) m lak (* Find next *)
          else containsSteps3to5_Owner s csr lak
      | _ => containsSteps3to5_Owner s csr lak
      end
  | Done => False
  end.

Lemma containsSteps3to5_Owner_lemma : forall s iniTPM ini finTPM fin csr lak,
  seq_execute (iniTPM, ini) s (finTPM, fin) ->
  In (pair csr (signature (hash csr) (pubToPrivKey lak))) fin ->
  ~ (In (pair csr (signature (hash csr) (pubToPrivKey lak))) ini) ->
  ~ (In (signature (hash csr) (pubToPrivKey lak)) ini) ->
  ~ (In (hash csr) ini) ->
  ~ (In (hash csr) iniTPM) ->
  containsSteps3to5_Owner s csr lak.
Proof.
  induction s; intros iniTPM ini finTPM fin csr lak E I N0 N1 N2 N3.
  - destruct c; simpl in *; inversion E; inversion H2; 
    subst; try (eapply IHs; fdeq);
    destruct (decEq csr m);
    subst; try eapply IHs; try eapply containsSteps4to5_Owner_lemma; fdeq.
  - inversion E; subst; congruence.
Qed.


(*
... ;; MakeCSR_LDevID attest cert ;;
... ;; TPM2_Hash (TCG_CSR_LDevID attest cert) ;;
... ;; TPM2_Sign (hash (TCG_CSR_LDevID attest cert)) (pubToPrivKey lak) ;;
... ;; MakePair (TCG_CSR_LDevID attest cert) 
                (signature (hash (TCG_CSR_LDevID attest cert)) (pubToPrivKey lak)) ;; ...
*)
Fixpoint containsSteps2to5_Owner (seq : sequence) (attest : message) (cert : signedCert) (lak : pubKey) : Prop :=
  match seq with
  | c ;; s => 
      match c with
      | MakeCSR_LDevID m crt => 
          if (decEq attest m) 
          then (
            if (decEq cert crt)
            then containsSteps3to5_Owner s (TCG_CSR_LDevID m crt) lak (* Find next *)
            else containsSteps2to5_Owner s attest cert lak )
          else containsSteps2to5_Owner s attest cert lak
      | _ => containsSteps2to5_Owner s attest cert lak
      end
  | Done => False
  end.

Lemma containsSteps2to5_Owner_lemma : forall s iniTPM ini finTPM fin attest cert lak,
  seq_execute (iniTPM, ini) s (finTPM, fin) ->
  In (pair (TCG_CSR_LDevID attest cert)
           (signature (hash (TCG_CSR_LDevID attest cert)) (pubToPrivKey lak))) fin ->
  ~ (In (pair (TCG_CSR_LDevID attest cert)
              (signature (hash (TCG_CSR_LDevID attest cert)) (pubToPrivKey lak))) ini) ->
  ~ (In (signature (hash (TCG_CSR_LDevID attest cert)) (pubToPrivKey lak)) ini) ->
  ~ (In (hash (TCG_CSR_LDevID attest cert)) ini) ->
  ~ (In (hash (TCG_CSR_LDevID attest cert)) iniTPM) ->
  ~ (In (TCG_CSR_LDevID attest cert) ini) ->
  containsSteps2to5_Owner s attest cert lak.
Proof.
  induction s; intros iniTPM ini finTPM fin attest cert lak E I N0 N1 N2 N2_TPM N3.
  - destruct c; simpl in *; inversion E; inversion H2; 
    subst; try (eapply IHs; fdeq).
    destruct (decEq attest m);
    destruct (decEq cert s0);
    subst; try eapply IHs; try eapply containsSteps3to5_Owner_lemma; fdeq.
  - inversion E; subst; congruence.
Qed.


(*
... ;; TPM2_Certify lak (pubToPrivKey iak) ;;
... ;; MakeCSR_LDevID (signature (TPM2B_Attest lak) (pubToPrivKey iak)) cert ;;
... ;; TPM2_Hash 
          (TCG_CSR_LDevID (signature (TPM2B_Attest lak) (pubToPrivKey iak)) cert) ;;
... ;; TPM2_Sign 
          (hash (TCG_CSR_LDevID (signature (TPM2B_Attest lak) (pubToPrivKey iak)) cert)) 
          (pubToPrivKey lak) ;;
... ;; MakePair 
          (TCG_CSR_LDevID (signature (TPM2B_Attest lak) (pubToPrivKey iak)) cert) 
          (signature 
            (hash (TCG_CSR_LDevID (signature (TPM2B_Attest lak) (pubToPrivKey iak)) cert)) 
            (pubToPrivKey lak)) ;; ...
*)
Fixpoint containsSteps1to5_Owner (seq : sequence) (iak lak : pubKey) (cert : signedCert) : Prop :=
  match seq with
  | c ;; s => 
      match c with
      | TPM2_Certify k k0' => 
          if (decEq lak k)
          then (
            if (decEq (pubToPrivKey iak) k0')
            then containsSteps2to5_Owner s (signature (TPM2B_Attest k) k0') cert k  (* Find next *)
            else containsSteps1to5_Owner s iak lak cert )
          else containsSteps1to5_Owner s iak lak cert
      | _ => containsSteps1to5_Owner s iak lak cert
      end
  | Done => False
  end.

Lemma containsSteps1to5_Owner_lemma : forall s iniTPM ini finTPM fin iak lak cert,
  seq_execute (iniTPM, ini) s (finTPM, fin) ->
  In (pair (TCG_CSR_LDevID (signature (TPM2B_Attest lak) (pubToPrivKey iak)) cert)
           (signature 
              (hash (TCG_CSR_LDevID (signature (TPM2B_Attest lak) (pubToPrivKey iak)) cert)) 
              (pubToPrivKey lak))) fin ->
  ~ (In (pair (TCG_CSR_LDevID (signature (TPM2B_Attest lak) (pubToPrivKey iak)) cert)
              (signature 
                  (hash (TCG_CSR_LDevID (signature (TPM2B_Attest lak) (pubToPrivKey iak)) cert)) 
                  (pubToPrivKey lak))) ini) ->
  ~ (In (signature 
          (hash (TCG_CSR_LDevID (signature (TPM2B_Attest lak) (pubToPrivKey iak)) cert)) 
          (pubToPrivKey lak)) ini) ->
  ~ (In (hash (TCG_CSR_LDevID (signature (TPM2B_Attest lak) (pubToPrivKey iak)) cert)) ini) ->
  ~ (In (hash (TCG_CSR_LDevID (signature (TPM2B_Attest lak) (pubToPrivKey iak)) cert)) iniTPM) ->
  ~ (In (TCG_CSR_LDevID (signature (TPM2B_Attest lak) (pubToPrivKey iak)) cert) ini) ->
  ~ (In (signature (TPM2B_Attest lak) (pubToPrivKey iak)) ini) ->
  ~ (In (TPM2B_Attest lak) ini) ->
  ~ (In (TPM2B_Attest lak) iniTPM) ->
  containsSteps1to5_Owner s iak lak cert.
Proof.
  induction s; intros iniTPM ini finTPM fin iak lak cert E I N0 N1 N2 N2_TPM N3 N4 N5 N5_TPM.
  - destruct c; simpl in *; inversion E; inversion H2;  
    subst; try (eapply IHs; fdeq);
    destruct (decEq lak (Public i r s1 d));
    destruct (decEq (pubToPrivKey iak) (Private i0 r0 Signing d0));
    subst; try eapply IHs; try eapply containsSteps2to5_Owner_lemma; try fdeq.
    rewrite <- e0; assumption.
  - inversion E; subst; congruence.
Qed.






Module Type LAK_Cert_Protocol.


(* Owner parameters *)
  Parameter pubLAK : pubKey.
  Parameter pubIAK : pubKey.
  Parameter certIAK : signedCert.

(* CA parameters *)
  Parameter pubCA : pubKey.
  Parameter pubOEM : pubKey.

(* All keys must be distinct *)
  Axiom keys_distinct :
    pubLAK <> pubIAK /\
    pubLAK <> pubCA /\
    pubLAK <> pubOEM /\
    pubIAK <> pubCA /\
    pubIAK <> pubOEM /\
    pubCA <> pubOEM.

  Definition privLAK := pubToPrivKey pubLAK.
  Definition privIAK := pubToPrivKey pubIAK.
  Definition privCA := pubToPrivKey pubCA.





(* Correct protocol steps of owner *)
  Definition steps1to5_Owner : sequence :=
    TPM2_Certify pubLAK privIAK ;;
    MakeCSR_LDevID (signature (TPM2B_Attest pubLAK) privIAK) certIAK ;;
    TPM2_Hash (TCG_CSR_LDevID (signature (TPM2B_Attest pubLAK) privIAK) certIAK) ;;
    TPM2_Sign (hash (TCG_CSR_LDevID (signature (TPM2B_Attest pubLAK) privIAK) certIAK)) privLAK ;;
    MakePair (TCG_CSR_LDevID (signature (TPM2B_Attest pubLAK) privIAK) certIAK) 
             (signature (hash (TCG_CSR_LDevID (signature (TPM2B_Attest pubLAK) privIAK) certIAK)) privLAK) ;;
    Done.


(* Candidate minimal initial state of owner *)

  Definition minTPM_Owner : tpm_state :=
  [ privateKey privLAK ;
    privateKey privIAK ].

  Definition min_Owner : state :=
  [ signedCertificate certIAK ].




(* The candidate minimal initial state is 
   a subset of every possible initial state,
   so it is a lower bound *)
  Lemma min_Owner_lowerBound :
    lower_bound steps1to5_Owner minTPM_Owner min_Owner.
  Proof.
    unfold lower_bound.
    intros iniTPM ini fin E;
(* Split steps_Owner into its individual commands *)
    inversion E as [initial mid1 final command steps_Owner' H_Certify E1| ]; subst;
    inversion E1 as [initial mid2 final command steps_Owner' H_MakeCSR E2| ]; subst;
    inversion E2 as [initial mid3 final command steps_Owner' H_Hash E3| ]; subst;
    inversion E3 as [initial mid4 final command steps_Owner' H_Sign E4| ]; subst;
    inversion E4 as [initial mid5 final command steps_Owner' H_MakePair E5| ]; subst;
    inversion E5; subst;
(* Invert each individual step in reverse order *) 
    inversion H_MakePair; subst; 
    inversion H_Sign; subst;
    inversion H_Hash; subst;
    inversion H_MakeCSR; subst;
    inversion H_Certify; subst;
(* Clear all hypothesis other than state requirements and key definitions *)
    clear E E1 E2 E3 E4 E5;
    clear H_Certify H_MakeCSR H_Hash H_Sign H_MakePair;
    split.
(* Case TPM state with Restricted Signing key *)
    - unfold minTPM_Owner; intros m' I; inversion I; subst.
    -- rewrite <- H0; inversion H5 as [EQ_false | H5']; subst.
        inversion EQ_false.
       inversion H5' as [EQ_false | H5'']; subst. 
        inversion EQ_false.
        assumption.
    -- inversion H; subst.
    --- rewrite <- H10; assumption.
    --- inversion H1.
(* Case state with Restricted Signing key *)
    - unfold min_Owner; intros m I; inversion I; subst.
    -- inversion H11 as [EQ_false | H11']; subst.
        inversion EQ_false.
        assumption.
    -- inversion H.
(* Case TPM state with Non-Restricted Signing key *)
    - unfold minTPM_Owner; intros m I; inversion I; subst.
    -- rewrite <- H0; inversion H5 as [EQ_false | H5']; subst. 
        inversion EQ_false.
       inversion H5' as [EQ_false | H5'']; subst. 
        inversion EQ_false.
        assumption.
    -- inversion H; subst.
    --- rewrite <- H10; assumption.
    --- inversion H1.
(* Case state with Non-Restricted Signing key *)
    - unfold min_Owner; intros m I; inversion I; subst.
    -- inversion H11 as [EQ_false | H11']; subst. 
         inversion EQ_false.
         assumption.
    -- inversion H.
  Qed.





(* The CA is trusted to have a good initial state *)
  Definition iniTPM_CA : tpm_state :=
  [ privateKey privCA ;
    publicKey pubCA ].

  Definition ini_CA : state :=
  [ publicKey pubOEM ;
    privateKey privCA ;
    publicKey pubCA ].

  Axiom CA_keys_good :
    caKey pubCA /\
    caKey pubOEM.




(* Protocol steps of CA *)
(* The CA waits to recieve a message from the owner. *)
(* That message must be in a specific form to be considered a proper request. *)
(* The CA will then execute its protocol steps on the input message. *)
(* If the protocol succeeds the CA will issue certificate [Cert k_LAK dev_id privCA] to the owner. *)
  Definition steps_CA (msg : message) (iak lak : pubKey) (cert : signedCert) : Prop :=
    match msg with
    | (pair (TCG_CSR_LDevID (signature (TPM2B_Attest k) k0') 
                            (Cert k0 id k_ca'))
            (signature m k')) =>
          iak = k0 /\
          lak = k /\
          cert = (Cert k0 id k_ca') /\
          seq_execute (iniTPM_CA, inferFrom m ++ ini_CA)
                            (CheckHash m
                                      (TCG_CSR_LDevID (signature (TPM2B_Attest k) k0') 
                                                      (Cert k0 id k_ca')) ;;
                            CheckSig (signature m k') k ;;
                            CheckSig (signature (TPM2B_Attest k) k0') k0 ;;
                            CheckCert (Cert k0 id k_ca') pubOEM ;;
                            CheckAttributes k Restricting Signing NonDecrypting ;;
                            Done)
                            (iniTPM_CA, 
                            inferFrom m ++ ini_CA)
    | _ => False
    end.


(* The candidate minimal initial state allows 
   the owner's protocol steps to succeed, 
   so it is in fact the minimum *)
  Lemma min_Owner_sufficient : forall m,
    attestationKey pubIAK ->
    steps_CA m pubIAK pubLAK certIAK ->
    sufficient steps1to5_Owner minTPM_Owner min_Owner.
  Proof.
    unfold sufficient. 
    intros m goodIAK CA;
    unfold minTPM_Owner, min_Owner, steps1to5_Owner, privIAK, privLAK;
    destruct pubIAK, r, s, d; simpl in goodIAK; try inversion goodIAK;
    destruct m; try inversion CA;
    destruct m1; try inversion CA;
    destruct m1; try inversion CA;
    destruct m1; try inversion CA;
    destruct s; try inversion CA;
    destruct m2; try inversion CA; subst;
    destruct H0; subst; destruct H0; subst;
    clear CA; simpl in *;
    inversion H0 as [initial mid1 final command steps_Owner' H_CheckHash H1 | ]; subst; 
    inversion H1 as [initial mid2 final command steps_Owner' H_CheckSig1 H2 | ]; subst;
    inversion H2 as [initial mid3 final command steps_Owner' H_CheckSig2 H3 | ]; subst;
    inversion H3 as [initial mid4 final command steps_Owner' H_CheckCert H4 | ]; subst;
    inversion H4 as [initial mid5 final command steps_Owner' H_CheckAttributes H5 | ]; subst;
    inversion H5; subst;
    inversion H_CheckAttributes; subst;
    simpl; trivial;
    eexists; simpl; repeat eapply SE_Seq; econstructor; simpl; auto.
  Qed.

  Lemma ca_implies_containsSteps1to5 : forall s iniTPM ini finTPM fin m iak lak cert,
    seq_execute (iniTPM, ini) s (finTPM, fin) ->
    In m fin ->
    (forall m', needsGenerated m' -> ~ In m' iniTPM) ->
    (forall m', needsGenerated m' -> ~ In m' ini) ->
    steps_CA m iak lak cert -> 
    containsSteps1to5_Owner s iak lak cert.
  Proof.
    intros s iniTPM ini finTPM fin m iak lak cert E I N_TPM N CA.
(* Get m into the form of the match statement in steps_CA *)
    destruct m; try inversion CA;
    destruct m1; try inversion CA;
    destruct m1; try inversion CA;
    destruct m1; try inversion CA;
    destruct s0; try inversion CA;
    destruct m2; try inversion CA; subst;
    destruct H0; subst; destruct H0; subst;
    clear CA; simpl in *.
(* Split steps_CA into its individual commands *)
    inversion H0 as [initial mid1 final command steps_Owner' H_CheckHash H1 | ]; subst; 
    inversion H1 as [initial mid2 final command steps_Owner' H_CheckSig1 H2 | ]; subst;
    inversion H2 as [initial mid3 final command steps_Owner' H_CheckSig2 H3 | ]; subst;
    inversion H3 as [initial mid4 final command steps_Owner' H_CheckCert H4 | ]; subst;
    inversion H4 as [initial mid5 final command steps_Owner' H_CheckAttributes H5 | ]; subst;
    inversion H5; subst;
(* Invert each individual step in reverse order *) 
    inversion H_CheckAttributes; subst;
    inversion H_CheckCert; subst;
    inversion H_CheckSig2; subst;
    inversion H_CheckSig1; subst;
    inversion H_CheckHash; subst.
(* Apply lemma *)
    eapply containsSteps1to5_Owner_lemma; eauto; 
    try apply N; try apply N_TPM; simpl; trivial.
  Qed.



  Lemma containsSteps1to5_implies_certify : forall s iak lak cert,
    containsSteps1to5_Owner s iak lak cert ->
    command_in_sequence s (TPM2_Certify lak (pubToPrivKey iak)).
  Proof.
    induction s; intros iak lak cert H0.
    - simpl; destruct (decEq (TPM2_Certify lak (pubToPrivKey iak)) c);
      [ trivial
      | apply IHs with (cert := cert);
        destruct c; simpl in *; try fdeq ].
      destruct (decEq lak p); 
      destruct (decEq (pubToPrivKey iak) p0); subst; congruence.
    - inversion H0.
  Qed.
(*
  Lemma containsSteps1to5_Owner_implies_sign : forall s iak lak cert,
    containsSteps1to5_Owner s iak lak cert ->
    exists hsh, command_in_sequence s (TPM2_Sign hsh (pubToPrivKey lak)).
  Proof.
    intros s iak lak cert H0.
    exists (hash (TCG_CSR_LDevID (signature (TPM2B_Attest pubLAK) privIAK) certIAK)).
    generalize dependent cert. generalize dependent lak. generalize dependent iak.
    induction s; intros.
    simpl. destruct (decEq
    (TPM2_Sign
       (hash
          (TCG_CSR_LDevID
             (signature (TPM2B_Attest pubLAK) privIAK) certIAK))
       (pubToPrivKey lak)) c).
       trivial.
      eapply IHs. destruct c; try (simpl in *; fdeq; fail). simpl in *.
      destruct (decEq lak p);
      destruct (decEq (pubToPrivKey iak) p0); subst; try congruence. *)

  Lemma certify_implies_lakInTPM : forall s iniTPM ini finTPM fin iak lak,
    seq_execute (iniTPM, ini) s (finTPM, fin) -> 
    command_in_sequence s (TPM2_Certify lak (pubToPrivKey iak)) ->
    In (privateKey (pubToPrivKey lak)) iniTPM.
  Proof.
    induction s; intros iniTPM ini finTPM fin iak lak E CI.
    - simpl in *; destruct (decEq (TPM2_Certify lak (pubToPrivKey iak)) c); inversion E; subst.
    -- inversion H2; assumption.
    -- destruct mid as [midTPM mid]; eapply exec_cannotGenerateKey; eauto.
    - inversion CI.
  Qed.


  Lemma certify_implies_iakInTPM : forall s iniTPM ini finTPM fin iak lak,
    seq_execute (iniTPM, ini) s (finTPM, fin) -> 
    command_in_sequence s (TPM2_Certify lak (pubToPrivKey iak)) ->
    In (privateKey (pubToPrivKey iak)) iniTPM.
  Proof.
    induction s; intros iniTPM ini finTPM fin iak lak E CI.
    - simpl in *; destruct (decEq (TPM2_Certify lak (pubToPrivKey iak)) c); inversion E; subst.
    -- inversion H2; assumption.
    -- destruct mid as [midTPM mid]; eapply exec_cannotGenerateKey; eauto.
    - inversion CI.
  Qed.




(* PROTOCOL ASSURANCES *)
(* Given the following assumptions: 
      The Owner executes some sequence of steps
      resulting in a message in its final state
      when only keys and certificates may be in its initial states.
      The CA's protocol executes successfully on the given message.
*)

(* Conclude:
      The private IAK and private LAK reside in the same TPM *)
  Theorem lak_and_iak_in_TPM : forall s iniTPM ini finTPM fin m iak lak cert,
    seq_execute (iniTPM, ini) s (finTPM, fin) -> 
    In m fin ->
    (forall m', needsGenerated m' -> ~ In m' iniTPM) ->
    (forall m', needsGenerated m' -> ~ In m' ini) ->
    steps_CA m iak lak cert ->
    In (privateKey (pubToPrivKey lak)) iniTPM /\ In (privateKey (pubToPrivKey iak)) iniTPM.
  Proof.
    intros s iniTPM ini finTPM fin m iak lak cert E I N_TPM N CA; 
    split; [ eapply certify_implies_lakInTPM | eapply certify_implies_iakInTPM ];
    eauto; eapply containsSteps1to5_implies_certify; eapply ca_implies_containsSteps1to5; eauto.
  Qed.

(* Conclude:
      The LAK is a Restricted Signing NonDecrypting key *)
    Theorem lak_good_attributes : forall m iak lak cert,
      steps_CA m iak lak cert ->
      attestationKey lak.
    Proof.
      intros m iak lak cert CA;
      destruct m; try inversion CA;
      destruct m1; try inversion CA;
      destruct m1; try inversion CA;
      destruct m1; try inversion CA;
      destruct s; try inversion CA;
      destruct m2; try inversion CA; subst;
      destruct H0; subst; destruct H0; subst;
      clear CA; simpl in *.
      inversion H0 as [initial mid1 final command steps_Owner' H_CheckHash H1 | ]; subst; 
      inversion H1 as [initial mid2 final command steps_Owner' H_CheckSig1 H2 | ]; subst;
      inversion H2 as [initial mid3 final command steps_Owner' H_CheckSig2 H3 | ]; subst;
      inversion H3 as [initial mid4 final command steps_Owner' H_CheckCert H4 | ]; subst;
      inversion H4 as [initial mid5 final command steps_Owner' H_CheckAttributes H5 | ]; subst;
      inversion H5; subst;
      inversion H_CheckAttributes; subst;
      simpl; trivial.
    Qed.


End LAK_Cert_Protocol.






(* OEM creation of IAK certificate based on EK certificate *)
(* ******************************************************* *)

(* Supersequence intermediate definitions and lemmas *)

(*
... ;; MakePair csr sig ;; ...
*)
Fixpoint oem3 (seq : sequence) (csr sig : message) : Prop :=
  match seq with
  | c ;; s =>
      match c with
      | MakePair m1 m2 =>
          if (decEq csr m1)
          then (
            if (decEq sig m2)
            then True (* Done *)
            else oem3 s csr sig )
          else oem3 s csr sig
      | _ => oem3 s csr sig
      end
  | Done => False
  end.

Lemma oem3_lemma : forall s iniTPM ini finTPM fin csr sig,
  seq_execute (iniTPM, ini) s (finTPM, fin) ->
  In (pair csr sig) fin ->
  ~ (In (pair csr sig) ini) ->
  oem3 s csr sig.
Proof.
  induction s; intros iniTPM ini finTPM fin csr sig E I N0.
  - destruct c; simpl in *; inversion E; inversion H2; 
    subst; try (eapply IHs; fdeq);
    destruct (decEq csr m);
    destruct (decEq sig m0);
    subst; trivial; eapply IHs; fdeq.
  - inversion E; subst; congruence.
Qed.


(*
... ;; TPM2_Sign hsh (pubToPrivKey iak) ;; 
... ;; MakePair csr (signature hsh (pubToPrivKey iak)) ;; ...
*)
Fixpoint oem2 (seq : sequence) (hsh csr : message) (iak : pubKey) : Prop :=
  match seq with
  | c ;; s =>
      match c with
      | TPM2_Sign m k =>
          if (decEq hsh m)
          then (
            if (decEq (pubToPrivKey iak) k)
            then oem3 s csr (signature hsh (pubToPrivKey iak))  (* Find next *)
            else oem2 s hsh csr iak )
          else oem2 s hsh csr iak
      | _ => oem2 s hsh csr iak
      end
  | Done => False
  end.

Lemma oem2_lemma : forall s iniTPM ini finTPM fin hsh csr iak,
  seq_execute (iniTPM, ini) s (finTPM, fin) ->
  In (pair csr (signature hsh (pubToPrivKey iak))) fin ->
  ~ (In (pair csr (signature hsh (pubToPrivKey iak))) ini) ->
  ~ (In (signature hsh (pubToPrivKey iak)) ini) ->
  (forall k, hsh <> TPM2B_Attest k) ->
  oem2 s hsh csr iak.
Proof.
  induction s; intros iniTPM ini finTPM fin hsh csr iak E I N0 N1 NA.
  - destruct c; simpl in *; inversion E; inversion H2; 
    subst; try (eapply IHs; fdeq);
    destruct (decEq hsh m);
    try destruct (decEq (pubToPrivKey iak) (Private i Restricting Signing d));
    try destruct (decEq (pubToPrivKey iak) (Private i NonRestricting Signing d));
    subst; try eapply IHs; try eapply containsStep5_Owner_lemma; fdeq.
  - inversion E; subst; congruence.
Qed.


(*
... ;; TPM2_Hash csr ;;
... ;; TPM2_Sign (hash csr) (pubToPrivKey iak) ;;
... ;; MakePair csr (signature (hash csr) (pubToPrivKey iak)) ;; ...
*)
Fixpoint oem1 (seq : sequence) (csr : message) (iak : pubKey) : Prop :=
  match seq with
  | c ;; s => 
      match c with 
      | TPM2_Hash m => 
          if (decEq csr m)
          then oem2 s (hash m) m iak (* Find next *)
          else oem1 s csr iak
      | _ => oem1 s csr iak
      end
  | Done => False
  end.

Lemma oem1_lemma : forall s iniTPM ini finTPM fin csr iak,
  seq_execute (iniTPM, ini) s (finTPM, fin) ->
  In (pair csr (signature (hash csr) (pubToPrivKey iak))) fin ->
  ~ (In (pair csr (signature (hash csr) (pubToPrivKey iak))) ini) ->
  ~ (In (signature (hash csr) (pubToPrivKey iak)) ini) ->
  ~ (In (hash csr) ini) ->
  ~ (In (hash csr) iniTPM) ->
  oem1 s csr iak.
Proof.
  induction s; intros iniTPM ini finTPM fin csr iak E I N0 N1 N2 N3.
  - destruct c; simpl in *; inversion E; inversion H2; 
    subst; try (eapply IHs; fdeq);
    destruct (decEq csr m);
    subst; try eapply IHs; try eapply containsSteps4to5_Owner_lemma; fdeq.
  - inversion E; subst; congruence.
Qed.


(*
... ;; MakeCSR_IDevID ident cert iak ;;
... ;; TPM2_Hash (TCG_CSR_IDevID ident cert iak) ;;
... ;; TPM2_Sign (hash (TCG_CSR_IDevID ident cert iak)) (pubToPrivKey iak) ;;
... ;; MakePair (TCG_CSR_IDevID ident cert iak) 
                (signature (hash (TCG_CSR_IDevID ident cert iak)) (pubToPrivKey iak)) ;; ...
*)
Fixpoint oem0 (seq : sequence) (ident : identifier) (cert : signedCert) (iak : pubKey) : Prop :=
  match seq with
  | c ;; s => 
      match c with
      | MakeCSR_IDevID id crt k => 
          if (decEq ident id)
          then (
            if (decEq cert crt)
            then (
              if (decEq iak k)
              then oem1 s (TCG_CSR_IDevID id crt k) iak
              else oem0 s ident cert iak )
            else oem0 s ident cert iak )
          else oem0 s ident cert iak 
      | _ => oem0 s ident cert iak 
      end
  | Done => False
  end.

Lemma oem0_lemma : forall s iniTPM ini finTPM fin ident cert iak,
  seq_execute (iniTPM, ini) s (finTPM, fin) ->
  In (pair (TCG_CSR_IDevID ident cert iak)
           (signature (hash (TCG_CSR_IDevID ident cert iak)) (pubToPrivKey iak))) fin ->
  ~ (In (pair (TCG_CSR_IDevID ident cert iak) 
              (signature (hash (TCG_CSR_IDevID ident cert iak)) (pubToPrivKey iak))) ini) ->
  ~ (In (signature (hash (TCG_CSR_IDevID ident cert iak)) (pubToPrivKey iak)) ini) ->
  ~ (In (hash (TCG_CSR_IDevID ident cert iak)) ini) ->
  ~ (In (hash (TCG_CSR_IDevID ident cert iak)) iniTPM) ->
  ~ (In (TCG_CSR_IDevID ident cert iak) ini) ->
  oem0 s ident cert iak.
Proof.
  induction s; intros iniTPM ini finTPM fin ident cert iak E I N0 N1 N2 N2_TPM N3.
  - destruct c; simpl in *; inversion E; inversion H2; 
    subst; try (eapply IHs; fdeq).
    destruct (decEq ident i);
    destruct (decEq cert s0);
    destruct (decEq iak p);
    subst; try eapply IHs; try eapply oem1_lemma; fdeq.
  - inversion E; subst; congruence.
Qed.



Fixpoint oemG (seq : sequence) (ek iak : pubKey) (rand : randType) :=
  match seq with
  | c ;; s =>
      match c with
      | TPM2_ActivateCredential crd k' k0' =>
          match crd with
          | encryptedCredential n g k =>
              match n with
              | hash m =>
                  match m with
                  | publicKey k0 =>
                      if (decEq rand g)
                      then (
                        if (decEq ek k)
                        then (
                          if (decEq iak k0)
                          then (
                            if (decEq (pubToPrivKey ek) k')
                            then (
                              if (decEq (pubToPrivKey iak) k0')
                              then True
                              else oemG s ek iak rand )
                            else oemG s ek iak rand )
                          else oemG s ek iak rand )
                        else oemG s ek iak rand )
                      else oemG s ek iak rand 
                  | _ => oemG s ek iak rand
                  end
              | _ => oemG s ek iak rand
              end
          | _ => oemG s ek iak rand
          end
      | _ => oemG s ek iak rand
      end
  | Done => False
  end.






Module Type IAK_Cert_Protocol.


(* OEM parameters *)
  Parameter pubNewKey : pubKey.
  Parameter pubEK : pubKey.
  Parameter certEK : signedCert.
  Parameter devID : deviceInfoType.

(* CA parameters *)
  Parameter pubCA : pubKey.
  Parameter privCA : privKey.
  Parameter pubTM : pubKey.
  Parameter nonce : randType.

(* All keys must be distinct *)
  Axiom keys_distinct :
    pubNewKey <> pubEK /\
    pubNewKey <> pubCA /\
    pubNewKey <> pubTM /\
    pubEK <> pubCA /\
    pubEK <> pubTM /\
    pubCA <> pubTM.

  Definition privNewKey := pubToPrivKey pubNewKey.
  Definition privEK := pubToPrivKey pubEK.


(* Candidate minimal initial state of OEM *)
  Definition minTPM_OEM : tpm_state :=
  [ privateKey privNewKey ].

  Definition min_OEM : state :=
  [ publicKey pubNewKey ;
    signedCertificate certEK ].


(* Correct protocol first steps of OEM *)
  Definition steps1to4_OEM : sequence :=
    MakeCSR_IDevID (Device_info devID) certEK pubNewKey ;;
    TPM2_Hash (TCG_CSR_IDevID (Device_info devID) certEK pubNewKey) ;;
    TPM2_Sign (hash (TCG_CSR_IDevID (Device_info devID) certEK pubNewKey)) privNewKey ;;
    MakePair (TCG_CSR_IDevID (Device_info devID) certEK pubNewKey)
             (signature (hash (TCG_CSR_IDevID (Device_info devID) certEK pubNewKey)) privNewKey) ;;
    Done.


  Lemma min_OEM_lowerBound : 
    lower_bound steps1to4_OEM minTPM_OEM min_OEM.
  Proof.
    unfold lower_bound.
    intros iniTPM ini mid E.
(* split steps_Owner into its individual commands *)
    inversion E as [initial mid0 final command steps_Owner' H_MakeCSR E0| ]; subst;
    inversion E0 as [initial mid1 final command steps_Owner' H_Hash E1| ]; subst;
    inversion E1 as [initial mid2 final command steps_Owner' H_Sign E2| ]; subst;
    inversion E2 as [initial mid3 final command steps_Owner' H_MakePair E3| ]; subst;
    inversion E3; subst.
(* Invert each individual step in reverse order *)
    inversion H_MakePair; subst; 
    inversion H_Sign; subst;
    inversion H_Hash; subst;
    inversion H_MakeCSR; subst;
    clear E E0 E1 E2 E3;
    clear H_MakeCSR H_Hash H_Sign H_MakePair;
    split.
(* Case TPM state with Restricted signing *)
    - unfold minTPM_OEM; intros m I; inversion I; subst.
    -- rewrite <- H0; inversion H5 as [EQ_false | H5']; subst.
        inversion EQ_false.
        assumption.
    -- inversion H; subst.
(* Case state with Restricted signing *)
    - unfold min_OEM; intros m I; inversion I; subst.
    -- assumption.
    -- inversion H; subst.
    --- assumption.
    --- inversion H1.
(* Case TPM state with Non-Restricted signing*)
    - unfold minTPM_OEM; intros m I; inversion I; subst.
    -- rewrite <- H0; inversion H5 as [EQ_false | H5']; subst.
        inversion EQ_false.
        assumption.
    -- inversion H; subst.
(* Case state with Non-Restricted signing *)
    - unfold min_OEM; intros m I; inversion I; subst.
    -- assumption.
    -- inversion H; subst.
    --- assumption.
    --- inversion H1.
  Qed.




(* The CA is trusted to know have a good initial state *)
  Definition iniTPM_CA : tpm_state :=
  [ privateKey privCA ;
    publicKey pubCA ].

  Definition ini_CA : state :=
  [ publicKey pubTM ;
    privateKey privCA ;
    publicKey pubCA ].

  Axiom CA_keys_good :
    privCA = pubToPrivKey pubCA /\
    caKey pubCA /\
    caKey pubTM.


(* Protocol steps of CA *)
(* The CA waits to recieve a message from the OEM. *)
(* That message must be in a specific form to be considered a proper request. *)
(* The CA will then execute its protocol steps on the input message. *)
(* If the protocol succeeds the CA will issue a challenge [encryptedCredential (hash (publicKey k_NewKey)) nonce k_EK] to the OEM. *)
  Definition steps_CA (m : message) (ident : identifier) (ek iak : pubKey) (cert : signedCert) : Prop :=
    match m with
    | (pair (TCG_CSR_IDevID (Device_info dev_id) (Cert k_EK tpm_id k_TM') k_NewKey)
            (signature m_Hash k_NewKey')) =>
          ident = (Device_info dev_id) /\
          ek = k_EK /\
          iak = k_NewKey /\
          cert = (Cert k_EK tpm_id k_TM') /\
          seq_execute (iniTPM_CA, inferFrom m ++ ini_CA)
                            (CheckHash m_Hash 
                                      (TCG_CSR_IDevID (Device_info dev_id) (Cert k_EK tpm_id k_TM') k_NewKey) ;;
                            CheckSig (signature m_Hash k_NewKey') k_NewKey ;;
                            CheckCert (Cert k_EK tpm_id k_TM') pubTM ;;
                            CheckAttributes k_NewKey Restricting Signing NonDecrypting ;;
                            Done)
                            (iniTPM_CA, 
                             inferFrom m ++ ini_CA)
    | _ => False
    end.


  Lemma ca_implies_oem0 : forall s iniTPM ini midTPM mid m ident ek iak cert,
    seq_execute (iniTPM, ini) s (midTPM, mid) ->
    In m mid ->
    (forall m', needsGenerated m' -> ~ In m' iniTPM) ->
    (forall m', needsGenerated m' -> ~ In m' ini) ->
    steps_CA m ident ek iak cert -> 
    oem0 s ident cert iak.
  Proof.
    intros s iniTPM ini finTPM fin m ident ek iak cert E I N_TPM N CA.
(* Get m into the form of the match statement in steps_CA *)
    destruct m; try inversion CA;
    destruct m1; try inversion CA;
    destruct i; try inversion CA;
    destruct s0; try inversion CA;
    destruct m2; try inversion CA; subst;
    destruct H0; subst; destruct H0; subst; destruct H0; subst;
    clear CA; simpl in *.
(* Split steps_CA into its individual commands *)
    inversion H0 as [initial mid1 final command steps_Owner' H_CheckHash H1 | ]; subst; 
    inversion H1 as [initial mid2 final command steps_Owner' H_CheckSig H2 | ]; subst;
    inversion H2 as [initial mid4 final command steps_Owner' H_CheckCert H3 | ]; subst;
    inversion H3 as [initial mid5 final command steps_Owner' H_CheckAttributes H4 | ]; subst;
    inversion H4; subst;
(* Invert each individual step in reverse order *) 
    inversion H_CheckAttributes; subst;
    inversion H_CheckCert; subst;
    inversion H_CheckSig; subst;
    inversion H_CheckHash; subst.
(* Apply lemma *)
    eapply oem0_lemma; eauto; 
    try apply N; try apply N_TPM; simpl; trivial.
  Qed.



(* Correct protocol second steps of OEM *)
(* OEM waits to recieve challenge from the CA *)
  Definition step7_OEM (m : message) : sequence :=
    TPM2_ActivateCredential m privEK privNewKey ;;
    Done.

  
  Lemma rand_implies_oemG : forall s2 midTPM mid finTPM fin ek iak g,  
    seq_execute (midTPM, mid) s2 (finTPM, fin) ->
    In (encryptedCredential (hash (publicKey iak)) g ek) mid ->
    (forall ki ke, iak <> ki -> ~(In (encryptedCredential (hash (publicKey ki)) g ke) mid)) ->
    (forall ki ke, ek <> ke -> ~(In (encryptedCredential (hash (publicKey ki)) g ke) mid)) ->
    ~ (In (randomNum g)) mid ->
    In (randomNum g) fin ->
    oemG s2 ek iak g.
  Proof.
    induction s2; intros midTPM mid finTPM fin ek iak g E Im N_IAK N_EK N I.
    - destruct c; simpl in *; inversion E; inversion H2;
      subst; try (eapply IHs2; fdeq);
      try (eapply IHs2; 
      [ eauto 
      | simpl 
      | intros ki ke Neq; eapply exec_cannotGenerateCred_contrapositive 
      | intros ki ke Neq; eapply exec_cannotGenerateCred_contrapositive 
      | fdeq |  ]; eauto). 
      inversion H14; subst;
      destruct (decEq g g0);
      destruct (decEq ek (Public i r s0 d));
      destruct (decEq iak (Public i0 r0 s1 d0));
      destruct (decEq (pubToPrivKey ek) (Private i r s0 d));
      destruct (decEq (pubToPrivKey iak) (Private i0 r0 s1 d0)); subst; trivial;
      eapply IHs2; eauto; try (simpl; eauto; fail); try (intros ki ke Neq; eapply exec_cannotGenerateCred_contrapositive; eauto; fail);
      simpl in *; subst;
      try (destruct (N_IAK (Public i0 r0 s1 d0) (Public i r s0 d)); auto; fail);
      try (destruct (N_EK (Public i0 r0 s1 d0) (Public i r s0 d)); auto; fail);
      fdeq.
    - inversion E; subst; congruence.
  Qed.



  Lemma ca_and_rand_implies_oemG : forall s2 s1 iniTPM ini midTPM mid finTPM fin m ident ek iak cert g,
    seq_execute (iniTPM, ini) s1 (midTPM, mid) -> 
    In m mid ->
    (forall m', needsGenerated m' -> ~ In m' iniTPM) ->
    (forall m', needsGenerated m' -> ~ In m' ini) ->
    steps_CA m ident ek iak cert ->
    seq_execute (midTPM, inferFrom (encryptedCredential (hash (publicKey iak)) g ek) ++ mid) 
                 s2 
                (finTPM, fin) ->
    In (randomNum g) fin ->
    oemG s2 ek iak g.
  Proof.
    intros s2 s1 iniTPM ini midTPM mid finTPM fin m ident ek iak cert g.
    intros E1 Im N_TPM N CA E2 Ig.

    destruct m; try inversion CA;
    destruct m1; try inversion CA;
    destruct i; try inversion CA;
    destruct s; try inversion CA;
    destruct m2; try inversion CA; subst;
    destruct H0; subst; destruct H0; subst; destruct H0; subst;
    clear CA; simpl in *.

    inversion H0 as [initial mid1 final command steps_Owner' H_CheckHash H1 | ]; subst; 
    inversion H1 as [initial mid2 final command steps_Owner' H_CheckSig H2 | ]; subst;
    inversion H2 as [initial mid4 final command steps_Owner' H_CheckCert H3 | ]; subst;
    inversion H3 as [initial mid5 final command steps_Owner' H_CheckAttributes H4 | ]; subst;
    inversion H4; subst.

    inversion H_CheckAttributes; subst;
    inversion H_CheckCert; subst;
    inversion H_CheckSig; subst;
    inversion H_CheckHash; subst.

    eapply rand_implies_oemG;
    [ eauto 
    | simpl; eauto 
    | intros ki ke Neq
    | intros ki ke Neq
    | intros HC; inversion HC; try congruence; generalize dependent H; 
      eapply seq_exec_cannotGenerateRand_contrapositive;
      eauto ; try (intros n k); apply N; simpl; auto
    |  eauto ];

    intros HC; inversion HC; try congruence; generalize dependent H;
    eapply seq_exec_cannotGenerateCred_contrapositive; 
    eauto; apply N; simpl; auto.
  Qed.


  Lemma oemG_implies_activatecredential : forall s2 ek iak g,
    oemG s2 ek iak g ->
    command_in_sequence s2 
                       (TPM2_ActivateCredential (encryptedCredential (hash (publicKey iak)) g ek) 
                                                (pubToPrivKey ek) 
                                                (pubToPrivKey iak)).
  Proof.
    induction s2; intros ek iak g H0; simpl.
    - destruct (decEq 
                  (TPM2_ActivateCredential (encryptedCredential (hash (publicKey iak)) g ek)
                                           (pubToPrivKey ek) 
                                           (pubToPrivKey iak)) 
                   c);
      [ trivial
      | apply IHs2; simpl in *;
        destruct c; try assumption;
        destruct m; subst; try assumption; 
        destruct m; subst; try assumption; 
        destruct m; subst; try assumption;        
        destruct (decEq g r);
        destruct (decEq ek p1);
        destruct (decEq iak p2);
        destruct (decEq (pubToPrivKey ek) p);
        destruct (decEq (pubToPrivKey iak) p0); 
        subst; congruence ].
    - inversion H0.
  Qed.


  Lemma activatecredential_implies_iakInTPM : forall s2 midTPM mid finTPM fin ek iak g,
    seq_execute (midTPM, mid) s2 (finTPM, fin) -> 
    command_in_sequence s2 
                      (TPM2_ActivateCredential (encryptedCredential (hash (publicKey iak)) g ek) 
                                               (pubToPrivKey ek) 
                                               (pubToPrivKey iak)) ->
    In (privateKey (pubToPrivKey iak)) midTPM.
  Proof.
    induction s2; intros midTPM mid finTPM fin ek iak g E CI.
    - simpl in *;
      destruct (decEq 
                  (TPM2_ActivateCredential (encryptedCredential (hash (publicKey iak)) g ek)
                                           (pubToPrivKey ek) 
                                           (pubToPrivKey iak)) 
                   c);
      inversion E; subst.
    -- inversion H2; assumption.
    -- destruct mid0 as [midTPM0 mid0]; eapply exec_cannotGenerateKey; eauto.
    - inversion CI.
  Qed.


  Lemma activatecredential_implies_ekInTPM : forall s2 midTPM mid finTPM fin ek iak g,
    seq_execute (midTPM, mid) s2 (finTPM, fin) -> 
    command_in_sequence s2 
                      (TPM2_ActivateCredential (encryptedCredential (hash (publicKey iak)) g ek) 
                                               (pubToPrivKey ek) 
                                               (pubToPrivKey iak)) ->
    In (privateKey (pubToPrivKey ek)) midTPM.
  Proof.
    induction s2; intros midTPM mid finTPM fin ek iak g E CI.
    - simpl in *;
      destruct (decEq 
                  (TPM2_ActivateCredential (encryptedCredential (hash (publicKey iak)) g ek)
                                           (pubToPrivKey ek) 
                                           (pubToPrivKey iak)) 
                  c);
      inversion E; subst.
    -- inversion H2; assumption.
    -- destruct mid0 as [midTPM0 mid0]; eapply exec_cannotGenerateKey; eauto.
    - inversion CI.
  Qed.


(* PROTOCOL ASSURANCES *)
(* Given the following assumptions: 
      The OEM executes some sequence of steps
      resulting in a message in its intermediate final state
      when only keys and certificates may be in its initial states.
      The CA's protocol executes successfully on the given message.
      The OEM executes some other sequence of steps upon receiving the CA's challenge
      resulting in the nonce in its final state.
*)

(* Conclude:
      The private EK and private IAK reside in the same TPM *)
  Theorem iak_and_ek_in_TPM : forall s2 s1 iniTPM ini midTPM mid finTPM fin m ident ek iak cert g,
    seq_execute (iniTPM, ini) s1 (midTPM, mid) -> 
    In m mid ->
    (forall m', needsGenerated m' -> ~ In m' iniTPM) ->
    (forall m', needsGenerated m' -> ~ In m' ini) ->
    steps_CA m ident ek iak cert ->
    seq_execute (midTPM, inferFrom (encryptedCredential (hash (publicKey iak)) g ek) ++ mid) 
                 s2 
                (finTPM, fin) ->
    In (randomNum g) fin ->
    In (privateKey (pubToPrivKey iak)) iniTPM /\ In (privateKey (pubToPrivKey ek)) iniTPM.
  Proof.
    intros s2 s1 iniTPM ini midTPM mid finTPM fin m ident ek iak cert g;
    intros E1 Im N_TPM N CA E2 Ig;
    split; eapply seq_exec_cannotGenerateKey; eauto; 
    [ eapply activatecredential_implies_iakInTPM | eapply activatecredential_implies_ekInTPM ]; eauto;
    eapply oemG_implies_activatecredential; eapply ca_and_rand_implies_oemG with (s1 := s1); eauto.
  Qed.


(* Conclude:
      The EK certificate is valid and signed by the TPM Manufacturer *)
  Theorem ek_certificate_valid : forall m ident ek iak cert,
    steps_CA m ident ek iak cert ->
    execute (iniTPM_CA, inferFrom m ++ ini_CA) 
            (CheckCert cert pubTM) 
            (iniTPM_CA, inferFrom m ++ ini_CA).
  Proof.
    intros m ident ek iak cert CA.

    destruct m; try inversion CA;
    destruct m1; try inversion CA;
    destruct i; try inversion CA;
    destruct s; try inversion CA;
    destruct m2; try inversion CA; subst;
    destruct H0; subst; destruct H0; subst; destruct H0; subst;
    clear CA; simpl in *.

    inversion H0 as [initial mid1 final command steps_Owner' H_CheckHash H1 | ]; subst; 
    inversion H1 as [initial mid2 final command steps_Owner' H_CheckSig H2 | ]; subst;
    inversion H2 as [initial mid4 final command steps_Owner' H_CheckCert H3 | ]; subst;
    inversion H3 as [initial mid5 final command steps_Owner' H_CheckAttributes H4 | ]; subst;
    inversion H4; subst.

    inversion H_CheckAttributes; subst;
    inversion H_CheckCert; subst;
    inversion H_CheckSig; subst;
    inversion H_CheckHash; subst.

    constructor; simpl; auto.
  Qed.

(* Conclude:
      The IAK is a Restricted Signing NonDecrypting key *)
  Theorem iak_good_attributes : forall m ident ek iak cert,
    steps_CA m ident ek iak cert ->
    attestationKey iak.
  Proof.
    intros m ident ek iak cert CA;
    destruct m; try inversion CA;
    destruct m1; try inversion CA;
    destruct i; try inversion CA;
    destruct s; try inversion CA;
    destruct m2; try inversion CA; subst;
    destruct H0; subst; destruct H0; subst; destruct H0; subst;
    clear CA; simpl in *.
    inversion H0 as [initial mid1 final command steps_Owner' H_CheckHash H1 | ]; subst; 
    inversion H1 as [initial mid2 final command steps_Owner' H_CheckSig H2 | ]; subst;
    inversion H2 as [initial mid4 final command steps_Owner' H_CheckCert H3 | ]; subst;
    inversion H3 as [initial mid5 final command steps_Owner' H_CheckAttributes H4 | ]; subst;
    inversion H4; subst.
    inversion H_CheckAttributes; subst;
    simpl; trivial.
  Qed.



End IAK_Cert_Protocol.

