module MLS.NetworkTypes

open Comparse

let mls_nat_pred (n:nat) = n < normalize_term (pow2 30)
let mls_nat_pred_eq (n:nat): Lemma(pow2 30 == normalize_term (pow2 30)) [SMTPat (mls_nat_pred n)] =
  assert_norm(pow2 30 == normalize_term (pow2 30))
type mls_nat = refined nat mls_nat_pred
val ps_mls_nat: #bytes:Type0 -> {| bytes_like bytes |} -> nat_parser_serializer bytes mls_nat_pred
let ps_mls_nat #bytes #bl =
  mk_trivial_isomorphism (refine ps_quic_nat mls_nat_pred)

val ps_mls_nat_length: #bytes:Type0 -> {| bytes_like bytes |} -> x:mls_nat -> Lemma
  (prefixes_length #bytes (ps_mls_nat.serialize x) == (
    if x < pow2 6 then 1
    else if x < pow2 14 then 2
    else 4
  ) /\
  pow2 6 == normalize_term (pow2 6) /\
  pow2 14 == normalize_term (pow2 14)
  )
  [SMTPat (prefixes_length #bytes (ps_mls_nat.serialize x))]
let ps_mls_nat_length #bytes #bl x = ()

type mls_bytes (bytes:Type0) {|bytes_like bytes|} = pre_length_bytes bytes mls_nat_pred
type mls_list (bytes:Type0) {|bytes_like bytes|} (#a:Type) (ps_a:parser_serializer bytes a) = pre_length_list ps_a mls_nat_pred

let ps_mls_bytes (#bytes:Type0) {|bytes_like bytes|}: parser_serializer bytes (mls_bytes bytes) = ps_pre_length_bytes mls_nat_pred ps_mls_nat
let ps_mls_list (#bytes:Type0) {|bytes_like bytes|} (#a:Type) (ps_a:parser_serializer bytes a): parser_serializer bytes (mls_list bytes ps_a) = ps_pre_length_list #bytes mls_nat_pred ps_mls_nat ps_a

/// opaque HPKEPublicKey<V>;

type hpke_public_key_nt (bytes:Type0) {|bytes_like bytes|} = mls_bytes bytes
val ps_hpke_public_key_nt: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (hpke_public_key_nt bytes)
let ps_hpke_public_key_nt #bytes #bl = ps_mls_bytes

/// enum {
///     reserved(0),
///     mls10(1),
///     (255)
/// } ProtocolVersion;

type protocol_version_nt =
  | PV_mls10: [@@@ with_num_tag 1 1] unit -> protocol_version_nt

%splice [ps_protocol_version_nt] (gen_parser (`protocol_version_nt))

/// uint16 CipherSuite;

type cipher_suite_nt =
  | CS_mls_128_dhkemx25519_aes128gcm_sha256_ed25519: [@@@ with_num_tag 2 1] unit -> cipher_suite_nt
  | CS_mls_128_dhkemp256_aes128gcm_sha256_p256: [@@@ with_num_tag 2 2] unit -> cipher_suite_nt
  | CS_mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519: [@@@ with_num_tag 2 3] unit -> cipher_suite_nt
  | CS_mls_256_dhkemx448_aes256gcm_sha512_ed448: [@@@ with_num_tag 2 4] unit -> cipher_suite_nt
  | CS_mls_256_dhkemp521_aes256gcm_sha512_p521: [@@@ with_num_tag 2 5] unit -> cipher_suite_nt
  | CS_mls_256_dhkemx448_chacha20poly1305_sha512_ed448: [@@@ with_num_tag 2 6] unit -> cipher_suite_nt
  | CS_mls_256_dhkemp384_aes256gcm_sha384_p384: [@@@ with_num_tag 2 7] unit -> cipher_suite_nt

%splice [ps_cipher_suite_nt] (gen_parser (`cipher_suite_nt))

/// // See IANA registry for registered values
/// uint16 ExtensionType;

type extension_type_nt: eqtype =
  | ET_application_id: [@@@ with_num_tag 2 0x0001] unit -> extension_type_nt
  | ET_ratchet_tree: [@@@ with_num_tag 2 0x0002] unit -> extension_type_nt
  | ET_required_capabilities: [@@@ with_num_tag 2 0x0003] unit -> extension_type_nt
  | ET_external_pub: [@@@ with_num_tag 2 0x0004] unit -> extension_type_nt
  | ET_external_senders: [@@@ with_num_tag 2 0x0005] unit -> extension_type_nt

%splice [ps_extension_type_nt] (gen_parser (`extension_type_nt))

/// struct {
///     ExtensionType extension_type;
///     opaque extension_data<V>;
/// } Extension;

type extension_nt (bytes:Type0) {|bytes_like bytes|} = {
  extension_type: extension_type_nt;
  extension_data: mls_bytes bytes;
}

%splice [ps_extension_nt] (gen_parser (`extension_nt))

/// struct {
///     uint8 present;
///     select (present) {
///         case 0: struct{};
///         case 1: T value;
///     }
/// } optional<T>;

[@@"opaque_to_smt"]
val ps_option: #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type0 -> parser_serializer bytes a -> parser_serializer bytes (option a)
let ps_option #bytes #bl #a ps_a =
  let n_pred = (fun n -> n <= 1) in
  let b_type (x:refined (nat_lbytes 1) n_pred): Type0 =
    if x = 1 then a else unit
  in
  mk_isomorphism (option a)
    (
      bind #_ #_ #_ #b_type (refine (ps_nat_lbytes 1) n_pred) (fun present ->
        if present = 1 then
          ps_a
        else
          ps_unit
      )
    )
  (fun (|present, x|) -> match present with
    | 0 -> None
    | 1 -> Some x
  )
  (fun x -> match x with
    | None -> (|0, ()|)
    | Some x -> (|1, x|)
  )

val ps_option_length: #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type0 -> ps_a:parser_serializer bytes a -> x:option a -> Lemma (
  prefixes_length ((ps_option ps_a).serialize x) == (
    match x with
    | None -> 1
    | Some y -> 1 + prefixes_length (ps_a.serialize y)
  ))
  [SMTPat (prefixes_length ((ps_option ps_a).serialize x))]
let ps_option_length #bytes #bl #a ps_a x =
  reveal_opaque (`%ps_option) (ps_option ps_a)

val ps_option_is_well_formed: #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type0 -> ps_a:parser_serializer bytes a -> pre:bytes_compatible_pre bytes -> x:option a -> Lemma (
  is_well_formed_partial (ps_option ps_a) pre x <==> (
    match x with
    | None -> True
    | Some y -> is_well_formed_partial ps_a pre y
  ))
  [SMTPat (is_well_formed_partial (ps_option ps_a) pre x)]
let ps_option_is_well_formed #bytes #bl #a ps_a pre x =
  reveal_opaque (`%ps_option) (ps_option ps_a)

/// struct {
///     ProtocolVersion version = mls10;
///     CipherSuite cipher_suite;
///     opaque group_id<V>;
///     uint64 epoch;
///     opaque tree_hash<V>;
///     opaque confirmed_transcript_hash<V>;
///     Extension extensions<V>;
/// } GroupContext;

type group_context_nt (bytes:Type0) {|bytes_like bytes|} = {
  version: protocol_version_nt;
  cipher_suite: cipher_suite_nt;
  group_id: mls_bytes bytes;
  epoch: nat_lbytes 8;
  tree_hash: mls_bytes bytes;
  confirmed_transcript_hash: mls_bytes bytes;
  extensions: mls_list bytes ps_extension_nt;
}

%splice [ps_group_context_nt] (gen_parser (`group_context_nt))



(*** Proposals ***)

/// uint16 ProposalType;

// Defined here because needed in TreeSync's proposal list in leaf node capabilities
// Actual sum type defined in TreeDEM.NetworkTypes
type proposal_type_nt =
  | PT_add: [@@@ with_num_tag 2 1] unit -> proposal_type_nt
  | PT_update: [@@@ with_num_tag 2 2] unit -> proposal_type_nt
  | PT_remove: [@@@ with_num_tag 2 3] unit -> proposal_type_nt
  | PT_psk: [@@@ with_num_tag 2 4] unit -> proposal_type_nt
  | PT_reinit: [@@@ with_num_tag 2 5] unit -> proposal_type_nt
  | PT_external_init: [@@@ with_num_tag 2 6] unit -> proposal_type_nt
  | PT_group_context_extensions: [@@@ with_num_tag 2 7] unit -> proposal_type_nt

%splice [ps_proposal_type_nt] (gen_parser (`proposal_type_nt))

