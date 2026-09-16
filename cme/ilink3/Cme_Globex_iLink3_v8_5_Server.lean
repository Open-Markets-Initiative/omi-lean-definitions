import Omi.Wire

/-!
# CME Group iLink 3 v8.5

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Exec Inst is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Server Simple Open Frame's Message Length is written from its body but not checked on decode, since the body has no bound the prefix must fit; the body is read by its content.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.CmeGlobexIlink3SbeV85Server

/-- Self Match Prevention Instruction: one byte code -/
def SelfMatchPreventionInstruction.codes : List UInt8 :=
  [0x4E, 0x4F]

inductive SelfMatchPreventionInstruction where
  | cancelNewest -- Cancel Newest
  | cancelOldest -- Cancel Oldest
  | unlisted (byte : { byte : UInt8 // byte ∉ SelfMatchPreventionInstruction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SelfMatchPreventionInstruction

def toByte : SelfMatchPreventionInstruction → UInt8
  | .cancelNewest => 0x4E
  | .cancelOldest => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SelfMatchPreventionInstruction :=
  if byte = 0x4E then .cancelNewest
  else .cancelOldest

def ofByte (byte : UInt8) : SelfMatchPreventionInstruction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SelfMatchPreventionInstruction) : ofByte value.toByte = value := by
  cases value with
  | cancelNewest => decide
  | cancelOldest => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SelfMatchPreventionInstruction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SelfMatchPreventionInstruction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SelfMatchPreventionInstruction) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SelfMatchPreventionInstruction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SelfMatchPreventionInstruction

/-- Cmta Giveup Cd: one byte code -/
def CmtaGiveupCd.codes : List UInt8 :=
  [0x47, 0x53]

inductive CmtaGiveupCd where
  | giveUp -- Give Up
  | sgXoffset -- Sg Xoffset
  | unlisted (byte : { byte : UInt8 // byte ∉ CmtaGiveupCd.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CmtaGiveupCd

def toByte : CmtaGiveupCd → UInt8
  | .giveUp => 0x47
  | .sgXoffset => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CmtaGiveupCd :=
  if byte = 0x47 then .giveUp
  else .sgXoffset

def ofByte (byte : UInt8) : CmtaGiveupCd :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CmtaGiveupCd) : ofByte value.toByte = value := by
  cases value with
  | giveUp => decide
  | sgXoffset => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CmtaGiveupCd) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CmtaGiveupCd × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CmtaGiveupCd) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CmtaGiveupCd) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CmtaGiveupCd

/-- Cust Order Handling Inst: one byte code -/
def CustOrderHandlingInst.codes : List UInt8 :=
  [0x43, 0x44, 0x47, 0x48, 0x57, 0x59]

inductive CustOrderHandlingInst where
  | fcMprovidedscreen -- Fc Mprovidedscreen
  | otherprovidedscreen -- Otherprovidedscreen
  | fcmapiCtaIx -- Fcmapi Cta Ix
  | algoEngine -- Algo Engine
  | deskElectronic -- Desk Electronic
  | clientElectronic -- Client Electronic
  | unlisted (byte : { byte : UInt8 // byte ∉ CustOrderHandlingInst.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CustOrderHandlingInst

def toByte : CustOrderHandlingInst → UInt8
  | .fcMprovidedscreen => 0x43
  | .otherprovidedscreen => 0x44
  | .fcmapiCtaIx => 0x47
  | .algoEngine => 0x48
  | .deskElectronic => 0x57
  | .clientElectronic => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CustOrderHandlingInst :=
  if byte = 0x43 then .fcMprovidedscreen
  else if byte = 0x44 then .otherprovidedscreen
  else if byte = 0x47 then .fcmapiCtaIx
  else if byte = 0x48 then .algoEngine
  else if byte = 0x57 then .deskElectronic
  else .clientElectronic

def ofByte (byte : UInt8) : CustOrderHandlingInst :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CustOrderHandlingInst) : ofByte value.toByte = value := by
  cases value with
  | fcMprovidedscreen => decide
  | otherprovidedscreen => decide
  | fcmapiCtaIx => decide
  | algoEngine => decide
  | deskElectronic => decide
  | clientElectronic => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CustOrderHandlingInst) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CustOrderHandlingInst × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CustOrderHandlingInst) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CustOrderHandlingInst) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CustOrderHandlingInst

/-- List Update Action: one byte code -/
def ListUpdateAction.codes : List UInt8 :=
  [0x41, 0x44]

inductive ListUpdateAction where
  | add -- Add
  | delete -- Delete
  | unlisted (byte : { byte : UInt8 // byte ∉ ListUpdateAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ListUpdateAction

def toByte : ListUpdateAction → UInt8
  | .add => 0x41
  | .delete => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ListUpdateAction :=
  if byte = 0x41 then .add
  else .delete

def ofByte (byte : UInt8) : ListUpdateAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ListUpdateAction) : ofByte value.toByte = value := by
  cases value with
  | add => decide
  | delete => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ListUpdateAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ListUpdateAction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ListUpdateAction) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ListUpdateAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ListUpdateAction

/-- Ord Type Optional: one byte code -/
def OrdTypeOptional.codes : List UInt8 :=
  [0x31, 0x32, 0x34, 0x4B]

inductive OrdTypeOptional where
  | marketWithProtection -- Market With Protection
  | limit -- Limit
  | stopLimit -- Stop Limit
  | marketWithLeftoverAsLimit -- Market With Leftover As Limit
  | unlisted (byte : { byte : UInt8 // byte ∉ OrdTypeOptional.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrdTypeOptional

def toByte : OrdTypeOptional → UInt8
  | .marketWithProtection => 0x31
  | .limit => 0x32
  | .stopLimit => 0x34
  | .marketWithLeftoverAsLimit => 0x4B
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrdTypeOptional :=
  if byte = 0x31 then .marketWithProtection
  else if byte = 0x32 then .limit
  else if byte = 0x34 then .stopLimit
  else .marketWithLeftoverAsLimit

def ofByte (byte : UInt8) : OrdTypeOptional :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrdTypeOptional) : ofByte value.toByte = value := by
  cases value with
  | marketWithProtection => decide
  | limit => decide
  | stopLimit => decide
  | marketWithLeftoverAsLimit => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrdTypeOptional) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrdTypeOptional × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrdTypeOptional) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OrdTypeOptional) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrdTypeOptional

/-- Execution Mode: one byte code -/
def ExecutionMode.codes : List UInt8 :=
  [0x41, 0x50]

inductive ExecutionMode where
  | aggressive -- Aggressive
  | passive -- Passive
  | unlisted (byte : { byte : UInt8 // byte ∉ ExecutionMode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExecutionMode

def toByte : ExecutionMode → UInt8
  | .aggressive => 0x41
  | .passive => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExecutionMode :=
  if byte = 0x41 then .aggressive
  else .passive

def ofByte (byte : UInt8) : ExecutionMode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExecutionMode) : ofByte value.toByte = value := by
  cases value with
  | aggressive => decide
  | passive => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExecutionMode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExecutionMode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExecutionMode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ExecutionMode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExecutionMode

/-- Ord Status: one byte code -/
def OrdStatus.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x34, 0x35, 0x38, 0x43, 0x55]

inductive OrdStatus where
  | new -- New
  | partiallyFilled -- Partially Filled
  | filled -- Filled
  | cancelled -- Cancelled
  | replaced -- Replaced
  | rejected -- Rejected
  | expired -- Expired
  | undefined -- Undefined
  | unlisted (byte : { byte : UInt8 // byte ∉ OrdStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrdStatus

def toByte : OrdStatus → UInt8
  | .new => 0x30
  | .partiallyFilled => 0x31
  | .filled => 0x32
  | .cancelled => 0x34
  | .replaced => 0x35
  | .rejected => 0x38
  | .expired => 0x43
  | .undefined => 0x55
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrdStatus :=
  if byte = 0x30 then .new
  else if byte = 0x31 then .partiallyFilled
  else if byte = 0x32 then .filled
  else if byte = 0x34 then .cancelled
  else if byte = 0x35 then .replaced
  else if byte = 0x38 then .rejected
  else if byte = 0x43 then .expired
  else .undefined

def ofByte (byte : UInt8) : OrdStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrdStatus) : ofByte value.toByte = value := by
  cases value with
  | new => decide
  | partiallyFilled => decide
  | filled => decide
  | cancelled => decide
  | replaced => decide
  | rejected => decide
  | expired => decide
  | undefined => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrdStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrdStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrdStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OrdStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrdStatus

/-- Dk Reason: one byte code -/
def DkReason.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x5A]

inductive DkReason where
  | unknownSecurity -- Unknown Security
  | wrongSide -- Wrong Side
  | quantityExceedsOrder -- Quantity Exceeds Order
  | noMatchingOrder -- No Matching Order
  | priceExceedsLimit -- Price Exceeds Limit
  | calculationDifference -- Calculation Difference
  | noMatchingExecutionReport -- No Matching Execution Report
  | other -- Other
  | unlisted (byte : { byte : UInt8 // byte ∉ DkReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DkReason

def toByte : DkReason → UInt8
  | .unknownSecurity => 0x41
  | .wrongSide => 0x42
  | .quantityExceedsOrder => 0x43
  | .noMatchingOrder => 0x44
  | .priceExceedsLimit => 0x45
  | .calculationDifference => 0x46
  | .noMatchingExecutionReport => 0x47
  | .other => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DkReason :=
  if byte = 0x41 then .unknownSecurity
  else if byte = 0x42 then .wrongSide
  else if byte = 0x43 then .quantityExceedsOrder
  else if byte = 0x44 then .noMatchingOrder
  else if byte = 0x45 then .priceExceedsLimit
  else if byte = 0x46 then .calculationDifference
  else if byte = 0x47 then .noMatchingExecutionReport
  else .other

def ofByte (byte : UInt8) : DkReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DkReason) : ofByte value.toByte = value := by
  cases value with
  | unknownSecurity => decide
  | wrongSide => decide
  | quantityExceedsOrder => decide
  | noMatchingOrder => decide
  | priceExceedsLimit => decide
  | calculationDifference => decide
  | noMatchingExecutionReport => decide
  | other => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DkReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DkReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DkReason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : DkReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DkReason

/-- Ord Status Trd Cxl: one byte code -/
def OrdStatusTrdCxl.codes : List UInt8 :=
  [0x47, 0x48]

inductive OrdStatusTrdCxl where
  | tradeCorrection -- Trade Correction
  | tradeCancel -- Trade Cancel
  | unlisted (byte : { byte : UInt8 // byte ∉ OrdStatusTrdCxl.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrdStatusTrdCxl

def toByte : OrdStatusTrdCxl → UInt8
  | .tradeCorrection => 0x47
  | .tradeCancel => 0x48
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrdStatusTrdCxl :=
  if byte = 0x47 then .tradeCorrection
  else .tradeCancel

def ofByte (byte : UInt8) : OrdStatusTrdCxl :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrdStatusTrdCxl) : ofByte value.toByte = value := by
  cases value with
  | tradeCorrection => decide
  | tradeCancel => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrdStatusTrdCxl) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrdStatusTrdCxl × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrdStatusTrdCxl) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OrdStatusTrdCxl) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrdStatusTrdCxl

/-- Exec Type: one byte code -/
def ExecType.codes : List UInt8 :=
  [0x47, 0x48]

inductive ExecType where
  | tradeCorrection -- Trade Correction
  | tradeCancel -- Trade Cancel
  | unlisted (byte : { byte : UInt8 // byte ∉ ExecType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExecType

def toByte : ExecType → UInt8
  | .tradeCorrection => 0x47
  | .tradeCancel => 0x48
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExecType :=
  if byte = 0x47 then .tradeCorrection
  else .tradeCancel

def ofByte (byte : UInt8) : ExecType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExecType) : ofByte value.toByte = value := by
  cases value with
  | tradeCorrection => decide
  | tradeCancel => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExecType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExecType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExecType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ExecType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExecType

/-- Mass Action Ord Typ: one byte code -/
def MassActionOrdTyp.codes : List UInt8 :=
  [0x32, 0x34]

inductive MassActionOrdTyp where
  | limit -- Limit
  | stopLimit -- Stop Limit
  | unlisted (byte : { byte : UInt8 // byte ∉ MassActionOrdTyp.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MassActionOrdTyp

def toByte : MassActionOrdTyp → UInt8
  | .limit => 0x32
  | .stopLimit => 0x34
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MassActionOrdTyp :=
  if byte = 0x32 then .limit
  else .stopLimit

def ofByte (byte : UInt8) : MassActionOrdTyp :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MassActionOrdTyp) : ofByte value.toByte = value := by
  cases value with
  | limit => decide
  | stopLimit => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MassActionOrdTyp) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MassActionOrdTyp × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MassActionOrdTyp) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MassActionOrdTyp) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MassActionOrdTyp

/-- Credentials -/
structure Credentials where
  credentialsData : Bounded 2 UInt8
  deriving DecidableEq, Repr

namespace Credentials

def encode (message : Credentials) : List UInt8 :=
  encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.credentialsData.val.length)
    ++ encodeMany Byte.encode message.credentialsData.val

def decode (bytes : List UInt8) : Option (Credentials × List UInt8) := do
  let (credentialsLength, bytes) ← decodeUIntLE 2 bytes
  let (credentialsData_, bytes) ← decodeMany Byte.decode credentialsLength.toNat bytes
  if fits_credentialsData : credentialsData_.length < 256 ^ 2 then
    pure ({ credentialsData := ⟨credentialsData_, fits_credentialsData⟩ }, bytes)
  else none

theorem encode_length_pos (message : Credentials) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Credentials) : (encode message).length ≤ 65537 := by
  have bound_credentialsData := message.credentialsData.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

@[simp] theorem decode_encode (message : Credentials) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 2 Byte.encode Byte.decode Byte.decode_encode]
  simp only [Option.bind_some]
  simp only [message.credentialsData.length_lt, ↓reduceDIte]
  rfl

end Credentials

/-- Negotiation Response -/
structure NegotiationResponse where
  uuid : BitVec 64
  requestTimestamp : BitVec 64
  secretKeySecureIdExpiration : BitVec 16
  faultToleranceIndicator : BitVec 8
  splitMsg : BitVec 8
  previousSeqNo : BitVec 32
  previousUuid : BitVec 64
  credentials : Credentials
  deriving DecidableEq, Repr

namespace NegotiationResponse

def encode (message : NegotiationResponse) : List UInt8 :=
  encodeUIntLE 8 message.uuid
    ++ encodeUIntLE 8 message.requestTimestamp
    ++ encodeUIntLE 2 message.secretKeySecureIdExpiration
    ++ encodeUInt 1 message.faultToleranceIndicator
    ++ encodeUInt 1 message.splitMsg
    ++ encodeUIntLE 4 message.previousSeqNo
    ++ encodeUIntLE 8 message.previousUuid
    ++ Credentials.encode message.credentials

def decode (bytes : List UInt8) : Option (NegotiationResponse × List UInt8) := do
  let (uuid, bytes) ← decodeUIntLE 8 bytes
  let (requestTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (secretKeySecureIdExpiration, bytes) ← decodeUIntLE 2 bytes
  let (faultToleranceIndicator, bytes) ← decodeUInt 1 bytes
  let (splitMsg, bytes) ← decodeUInt 1 bytes
  let (previousSeqNo, bytes) ← decodeUIntLE 4 bytes
  let (previousUuid, bytes) ← decodeUIntLE 8 bytes
  let (credentials, bytes) ← Credentials.decode bytes
  pure ({ uuid, requestTimestamp, secretKeySecureIdExpiration, faultToleranceIndicator, splitMsg, previousSeqNo, previousUuid, credentials }, bytes)

theorem encode_length_pos (message : NegotiationResponse) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : NegotiationResponse) : (encode message).length ≤ 65569 := by
  have bound_credentials := Credentials.encode_length_le message.credentials
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : NegotiationResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Credentials.decode_encode, Option.bind_some]
  rfl

end NegotiationResponse

/-- Negotiation Reject: 68 bytes -/
structure NegotiationReject where
  reason : Alpha 48
  uuid : BitVec 64
  requestTimestamp : BitVec 64
  errorCodes : BitVec 16
  faultToleranceIndicator : BitVec 8
  splitMsg : BitVec 8
  deriving DecidableEq, Repr

namespace NegotiationReject

def encode (message : NegotiationReject) : List UInt8 :=
  Alpha.encode message.reason
    ++ encodeUIntLE 8 message.uuid
    ++ encodeUIntLE 8 message.requestTimestamp
    ++ encodeUIntLE 2 message.errorCodes
    ++ encodeUInt 1 message.faultToleranceIndicator
    ++ encodeUInt 1 message.splitMsg

def decode (bytes : List UInt8) : Option (NegotiationReject × List UInt8) := do
  let (reason, bytes) ← Alpha.decode 48 bytes
  let (uuid, bytes) ← decodeUIntLE 8 bytes
  let (requestTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (errorCodes, bytes) ← decodeUIntLE 2 bytes
  let (faultToleranceIndicator, bytes) ← decodeUInt 1 bytes
  let (splitMsg, bytes) ← decodeUInt 1 bytes
  pure ({ reason, uuid, requestTimestamp, errorCodes, faultToleranceIndicator, splitMsg }, bytes)

@[simp] theorem encode_length (message : NegotiationReject) : (encode message).length = 68 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : NegotiationReject) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NegotiationReject) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end NegotiationReject

/-- Establishment Ack: 38 bytes -/
structure EstablishmentAck where
  uuid : BitVec 64
  requestTimestamp : BitVec 64
  nextSeqNo : BitVec 32
  previousSeqNo : BitVec 32
  previousUuid : BitVec 64
  keepAliveInterval : BitVec 16
  secretKeySecureIdExpiration : BitVec 16
  faultToleranceIndicator : BitVec 8
  splitMsg : BitVec 8
  deriving DecidableEq, Repr

namespace EstablishmentAck

def encode (message : EstablishmentAck) : List UInt8 :=
  encodeUIntLE 8 message.uuid
    ++ encodeUIntLE 8 message.requestTimestamp
    ++ encodeUIntLE 4 message.nextSeqNo
    ++ encodeUIntLE 4 message.previousSeqNo
    ++ encodeUIntLE 8 message.previousUuid
    ++ encodeUIntLE 2 message.keepAliveInterval
    ++ encodeUIntLE 2 message.secretKeySecureIdExpiration
    ++ encodeUInt 1 message.faultToleranceIndicator
    ++ encodeUInt 1 message.splitMsg

def decode (bytes : List UInt8) : Option (EstablishmentAck × List UInt8) := do
  let (uuid, bytes) ← decodeUIntLE 8 bytes
  let (requestTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (nextSeqNo, bytes) ← decodeUIntLE 4 bytes
  let (previousSeqNo, bytes) ← decodeUIntLE 4 bytes
  let (previousUuid, bytes) ← decodeUIntLE 8 bytes
  let (keepAliveInterval, bytes) ← decodeUIntLE 2 bytes
  let (secretKeySecureIdExpiration, bytes) ← decodeUIntLE 2 bytes
  let (faultToleranceIndicator, bytes) ← decodeUInt 1 bytes
  let (splitMsg, bytes) ← decodeUInt 1 bytes
  pure ({ uuid, requestTimestamp, nextSeqNo, previousSeqNo, previousUuid, keepAliveInterval, secretKeySecureIdExpiration, faultToleranceIndicator, splitMsg }, bytes)

@[simp] theorem encode_length (message : EstablishmentAck) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : EstablishmentAck) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EstablishmentAck) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end EstablishmentAck

/-- Establishment Reject: 72 bytes -/
structure EstablishmentReject where
  reason : Alpha 48
  uuid : BitVec 64
  requestTimestamp : BitVec 64
  nextSeqNo : BitVec 32
  errorCodes : BitVec 16
  faultToleranceIndicator : BitVec 8
  splitMsg : BitVec 8
  deriving DecidableEq, Repr

namespace EstablishmentReject

def encode (message : EstablishmentReject) : List UInt8 :=
  Alpha.encode message.reason
    ++ encodeUIntLE 8 message.uuid
    ++ encodeUIntLE 8 message.requestTimestamp
    ++ encodeUIntLE 4 message.nextSeqNo
    ++ encodeUIntLE 2 message.errorCodes
    ++ encodeUInt 1 message.faultToleranceIndicator
    ++ encodeUInt 1 message.splitMsg

def decode (bytes : List UInt8) : Option (EstablishmentReject × List UInt8) := do
  let (reason, bytes) ← Alpha.decode 48 bytes
  let (uuid, bytes) ← decodeUIntLE 8 bytes
  let (requestTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (nextSeqNo, bytes) ← decodeUIntLE 4 bytes
  let (errorCodes, bytes) ← decodeUIntLE 2 bytes
  let (faultToleranceIndicator, bytes) ← decodeUInt 1 bytes
  let (splitMsg, bytes) ← decodeUInt 1 bytes
  pure ({ reason, uuid, requestTimestamp, nextSeqNo, errorCodes, faultToleranceIndicator, splitMsg }, bytes)

@[simp] theorem encode_length (message : EstablishmentReject) : (encode message).length = 72 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : EstablishmentReject) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EstablishmentReject) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end EstablishmentReject

/-- Sequence: 14 bytes -/
structure Sequence where
  uuid : BitVec 64
  nextSeqNo : BitVec 32
  faultToleranceIndicator : BitVec 8
  keepAliveIntervalLapsed : BitVec 8
  deriving DecidableEq, Repr

namespace Sequence

def encode (message : Sequence) : List UInt8 :=
  encodeUIntLE 8 message.uuid
    ++ encodeUIntLE 4 message.nextSeqNo
    ++ encodeUInt 1 message.faultToleranceIndicator
    ++ encodeUInt 1 message.keepAliveIntervalLapsed

def decode (bytes : List UInt8) : Option (Sequence × List UInt8) := do
  let (uuid, bytes) ← decodeUIntLE 8 bytes
  let (nextSeqNo, bytes) ← decodeUIntLE 4 bytes
  let (faultToleranceIndicator, bytes) ← decodeUInt 1 bytes
  let (keepAliveIntervalLapsed, bytes) ← decodeUInt 1 bytes
  pure ({ uuid, nextSeqNo, faultToleranceIndicator, keepAliveIntervalLapsed }, bytes)

@[simp] theorem encode_length (message : Sequence) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : Sequence) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Sequence) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end Sequence

/-- Terminate: 67 bytes -/
structure Terminate where
  reason : Alpha 48
  uuid : BitVec 64
  requestTimestamp : BitVec 64
  errorCodes : BitVec 16
  splitMsg : BitVec 8
  deriving DecidableEq, Repr

namespace Terminate

def encode (message : Terminate) : List UInt8 :=
  Alpha.encode message.reason
    ++ encodeUIntLE 8 message.uuid
    ++ encodeUIntLE 8 message.requestTimestamp
    ++ encodeUIntLE 2 message.errorCodes
    ++ encodeUInt 1 message.splitMsg

def decode (bytes : List UInt8) : Option (Terminate × List UInt8) := do
  let (reason, bytes) ← Alpha.decode 48 bytes
  let (uuid, bytes) ← decodeUIntLE 8 bytes
  let (requestTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (errorCodes, bytes) ← decodeUIntLE 2 bytes
  let (splitMsg, bytes) ← decodeUInt 1 bytes
  pure ({ reason, uuid, requestTimestamp, errorCodes, splitMsg }, bytes)

@[simp] theorem encode_length (message : Terminate) : (encode message).length = 67 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : Terminate) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Terminate) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end Terminate

/-- Retransmission: 31 bytes -/
structure Retransmission where
  uuid : BitVec 64
  lastUuid : BitVec 64
  requestTimestamp : BitVec 64
  fromSeqNo : BitVec 32
  msgCount16 : BitVec 16
  splitMsg : BitVec 8
  deriving DecidableEq, Repr

namespace Retransmission

def encode (message : Retransmission) : List UInt8 :=
  encodeUIntLE 8 message.uuid
    ++ encodeUIntLE 8 message.lastUuid
    ++ encodeUIntLE 8 message.requestTimestamp
    ++ encodeUIntLE 4 message.fromSeqNo
    ++ encodeUIntLE 2 message.msgCount16
    ++ encodeUInt 1 message.splitMsg

def decode (bytes : List UInt8) : Option (Retransmission × List UInt8) := do
  let (uuid, bytes) ← decodeUIntLE 8 bytes
  let (lastUuid, bytes) ← decodeUIntLE 8 bytes
  let (requestTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (fromSeqNo, bytes) ← decodeUIntLE 4 bytes
  let (msgCount16, bytes) ← decodeUIntLE 2 bytes
  let (splitMsg, bytes) ← decodeUInt 1 bytes
  pure ({ uuid, lastUuid, requestTimestamp, fromSeqNo, msgCount16, splitMsg }, bytes)

@[simp] theorem encode_length (message : Retransmission) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : Retransmission) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Retransmission) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end Retransmission

/-- Retransmit Reject: 75 bytes -/
structure RetransmitReject where
  reason : Alpha 48
  uuid : BitVec 64
  lastUuid : BitVec 64
  requestTimestamp : BitVec 64
  errorCodes : BitVec 16
  splitMsg : BitVec 8
  deriving DecidableEq, Repr

namespace RetransmitReject

def encode (message : RetransmitReject) : List UInt8 :=
  Alpha.encode message.reason
    ++ encodeUIntLE 8 message.uuid
    ++ encodeUIntLE 8 message.lastUuid
    ++ encodeUIntLE 8 message.requestTimestamp
    ++ encodeUIntLE 2 message.errorCodes
    ++ encodeUInt 1 message.splitMsg

def decode (bytes : List UInt8) : Option (RetransmitReject × List UInt8) := do
  let (reason, bytes) ← Alpha.decode 48 bytes
  let (uuid, bytes) ← decodeUIntLE 8 bytes
  let (lastUuid, bytes) ← decodeUIntLE 8 bytes
  let (requestTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (errorCodes, bytes) ← decodeUIntLE 2 bytes
  let (splitMsg, bytes) ← decodeUInt 1 bytes
  pure ({ reason, uuid, lastUuid, requestTimestamp, errorCodes, splitMsg }, bytes)

@[simp] theorem encode_length (message : RetransmitReject) : (encode message).length = 75 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : RetransmitReject) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetransmitReject) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end RetransmitReject

/-- Not Applied: 17 bytes -/
structure NotApplied where
  uuid : BitVec 64
  fromSeqNo : BitVec 32
  msgCount : BitVec 32
  splitMsg : BitVec 8
  deriving DecidableEq, Repr

namespace NotApplied

def encode (message : NotApplied) : List UInt8 :=
  encodeUIntLE 8 message.uuid
    ++ encodeUIntLE 4 message.fromSeqNo
    ++ encodeUIntLE 4 message.msgCount
    ++ encodeUInt 1 message.splitMsg

def decode (bytes : List UInt8) : Option (NotApplied × List UInt8) := do
  let (uuid, bytes) ← decodeUIntLE 8 bytes
  let (fromSeqNo, bytes) ← decodeUIntLE 4 bytes
  let (msgCount, bytes) ← decodeUIntLE 4 bytes
  let (splitMsg, bytes) ← decodeUInt 1 bytes
  pure ({ uuid, fromSeqNo, msgCount, splitMsg }, bytes)

@[simp] theorem encode_length (message : NotApplied) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : NotApplied) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NotApplied) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end NotApplied

/-- Party Details Group: 22 bytes -/
structure PartyDetailsGroup where
  partyDetailId : Alpha 20
  partyDetailRole : BitVec 16
  deriving DecidableEq, Repr

namespace PartyDetailsGroup

def encode (message : PartyDetailsGroup) : List UInt8 :=
  Alpha.encode message.partyDetailId
    ++ encodeUIntLE 2 message.partyDetailRole

def decode (bytes : List UInt8) : Option (PartyDetailsGroup × List UInt8) := do
  let (partyDetailId, bytes) ← Alpha.decode 20 bytes
  let (partyDetailRole, bytes) ← decodeUIntLE 2 bytes
  pure ({ partyDetailId, partyDetailRole }, bytes)

@[simp] theorem encode_length (message : PartyDetailsGroup) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : PartyDetailsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PartyDetailsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end PartyDetailsGroup

/-- Party Details Groups -/
structure PartyDetailsGroups where
  blockLength : BitVec 16
  partyDetailsGroup : Bounded 1 PartyDetailsGroup
  deriving DecidableEq, Repr

namespace PartyDetailsGroups

def encode (message : PartyDetailsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.partyDetailsGroup.val.length)
    ++ encodeMany PartyDetailsGroup.encode message.partyDetailsGroup.val

def decode (bytes : List UInt8) : Option (PartyDetailsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (partyDetailsGroup_, bytes) ← decodeMany PartyDetailsGroup.decode numInGroup.toNat bytes
  if fits_partyDetailsGroup : partyDetailsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, partyDetailsGroup := ⟨partyDetailsGroup_, fits_partyDetailsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : PartyDetailsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : PartyDetailsGroups) : (encode message).length ≤ 5613 := by
  have bound_partyDetailsGroup := message.partyDetailsGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const PartyDetailsGroup.encode 22 PartyDetailsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : PartyDetailsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 PartyDetailsGroup.encode PartyDetailsGroup.decode PartyDetailsGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.partyDetailsGroup.length_lt, ↓reduceDIte]
  rfl

end PartyDetailsGroups

/-- Trd Reg Publications Group: 2 bytes -/
structure TrdRegPublicationsGroup where
  trdRegPublicationType : BitVec 8
  trdRegPublicationReason : BitVec 8
  deriving DecidableEq, Repr

namespace TrdRegPublicationsGroup

def encode (message : TrdRegPublicationsGroup) : List UInt8 :=
  encodeUInt 1 message.trdRegPublicationType
    ++ encodeUInt 1 message.trdRegPublicationReason

def decode (bytes : List UInt8) : Option (TrdRegPublicationsGroup × List UInt8) := do
  let (trdRegPublicationType, bytes) ← decodeUInt 1 bytes
  let (trdRegPublicationReason, bytes) ← decodeUInt 1 bytes
  pure ({ trdRegPublicationType, trdRegPublicationReason }, bytes)

@[simp] theorem encode_length (message : TrdRegPublicationsGroup) : (encode message).length = 2 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : TrdRegPublicationsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TrdRegPublicationsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end TrdRegPublicationsGroup

/-- Trd Reg Publications Groups -/
structure TrdRegPublicationsGroups where
  blockLength : BitVec 16
  trdRegPublicationsGroup : Bounded 1 TrdRegPublicationsGroup
  deriving DecidableEq, Repr

namespace TrdRegPublicationsGroups

def encode (message : TrdRegPublicationsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.trdRegPublicationsGroup.val.length)
    ++ encodeMany TrdRegPublicationsGroup.encode message.trdRegPublicationsGroup.val

def decode (bytes : List UInt8) : Option (TrdRegPublicationsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (trdRegPublicationsGroup_, bytes) ← decodeMany TrdRegPublicationsGroup.decode numInGroup.toNat bytes
  if fits_trdRegPublicationsGroup : trdRegPublicationsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, trdRegPublicationsGroup := ⟨trdRegPublicationsGroup_, fits_trdRegPublicationsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : TrdRegPublicationsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TrdRegPublicationsGroups) : (encode message).length ≤ 513 := by
  have bound_trdRegPublicationsGroup := message.trdRegPublicationsGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const TrdRegPublicationsGroup.encode 2 TrdRegPublicationsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : TrdRegPublicationsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 TrdRegPublicationsGroup.encode TrdRegPublicationsGroup.decode TrdRegPublicationsGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.trdRegPublicationsGroup.length_lt, ↓reduceDIte]
  rfl

end TrdRegPublicationsGroups

/-- Party Details Definition Request Ack -/
structure PartyDetailsDefinitionRequestAck where
  seqNum : BitVec 32
  uuid : BitVec 64
  memo : Alpha 75
  avgPxGroupId : Alpha 20
  partyDetailsListReqId : BitVec 64
  sendingTimeEpoch : BitVec 64
  selfMatchPreventionId : BitVec 64
  partyDetailRequestStatus : BitVec 8
  custOrderCapacity : BitVec 8
  clearingAccountType : BitVec 8
  selfMatchPreventionInstruction : SelfMatchPreventionInstruction
  avgPxIndicator : BitVec 8
  clearingTradePriceType : BitVec 8
  cmtaGiveupCd : CmtaGiveupCd
  custOrderHandlingInst : CustOrderHandlingInst
  listUpdateAction : ListUpdateAction
  partyDetailDefinitionStatus : BitVec 8
  executor : BitVec 64
  idmShortCode : BitVec 64
  possRetransFlag : BitVec 8
  splitMsg : BitVec 8
  partyDetailsGroups : PartyDetailsGroups
  trdRegPublicationsGroups : TrdRegPublicationsGroups
  deriving DecidableEq, Repr

namespace PartyDetailsDefinitionRequestAck

def encode (message : PartyDetailsDefinitionRequestAck) : List UInt8 :=
  encodeUIntLE 4 message.seqNum
    ++ encodeUIntLE 8 message.uuid
    ++ Alpha.encode message.memo
    ++ Alpha.encode message.avgPxGroupId
    ++ encodeUIntLE 8 message.partyDetailsListReqId
    ++ encodeUIntLE 8 message.sendingTimeEpoch
    ++ encodeUIntLE 8 message.selfMatchPreventionId
    ++ encodeUInt 1 message.partyDetailRequestStatus
    ++ encodeUInt 1 message.custOrderCapacity
    ++ encodeUInt 1 message.clearingAccountType
    ++ SelfMatchPreventionInstruction.encode message.selfMatchPreventionInstruction
    ++ encodeUInt 1 message.avgPxIndicator
    ++ encodeUInt 1 message.clearingTradePriceType
    ++ CmtaGiveupCd.encode message.cmtaGiveupCd
    ++ CustOrderHandlingInst.encode message.custOrderHandlingInst
    ++ ListUpdateAction.encode message.listUpdateAction
    ++ encodeUInt 1 message.partyDetailDefinitionStatus
    ++ encodeUIntLE 8 message.executor
    ++ encodeUIntLE 8 message.idmShortCode
    ++ encodeUInt 1 message.possRetransFlag
    ++ encodeUInt 1 message.splitMsg
    ++ PartyDetailsGroups.encode message.partyDetailsGroups
    ++ TrdRegPublicationsGroups.encode message.trdRegPublicationsGroups

def decode (bytes : List UInt8) : Option (PartyDetailsDefinitionRequestAck × List UInt8) := do
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (uuid, bytes) ← decodeUIntLE 8 bytes
  let (memo, bytes) ← Alpha.decode 75 bytes
  let (avgPxGroupId, bytes) ← Alpha.decode 20 bytes
  let (partyDetailsListReqId, bytes) ← decodeUIntLE 8 bytes
  let (sendingTimeEpoch, bytes) ← decodeUIntLE 8 bytes
  let (selfMatchPreventionId, bytes) ← decodeUIntLE 8 bytes
  let (partyDetailRequestStatus, bytes) ← decodeUInt 1 bytes
  let (custOrderCapacity, bytes) ← decodeUInt 1 bytes
  let (clearingAccountType, bytes) ← decodeUInt 1 bytes
  let (selfMatchPreventionInstruction, bytes) ← SelfMatchPreventionInstruction.decode bytes
  let (avgPxIndicator, bytes) ← decodeUInt 1 bytes
  let (clearingTradePriceType, bytes) ← decodeUInt 1 bytes
  let (cmtaGiveupCd, bytes) ← CmtaGiveupCd.decode bytes
  let (custOrderHandlingInst, bytes) ← CustOrderHandlingInst.decode bytes
  let (listUpdateAction, bytes) ← ListUpdateAction.decode bytes
  let (partyDetailDefinitionStatus, bytes) ← decodeUInt 1 bytes
  let (executor, bytes) ← decodeUIntLE 8 bytes
  let (idmShortCode, bytes) ← decodeUIntLE 8 bytes
  let (possRetransFlag, bytes) ← decodeUInt 1 bytes
  let (splitMsg, bytes) ← decodeUInt 1 bytes
  let (partyDetailsGroups, bytes) ← PartyDetailsGroups.decode bytes
  let (trdRegPublicationsGroups, bytes) ← TrdRegPublicationsGroups.decode bytes
  pure ({ seqNum, uuid, memo, avgPxGroupId, partyDetailsListReqId, sendingTimeEpoch, selfMatchPreventionId, partyDetailRequestStatus, custOrderCapacity, clearingAccountType, selfMatchPreventionInstruction, avgPxIndicator, clearingTradePriceType, cmtaGiveupCd, custOrderHandlingInst, listUpdateAction, partyDetailDefinitionStatus, executor, idmShortCode, possRetransFlag, splitMsg, partyDetailsGroups, trdRegPublicationsGroups }, bytes)

theorem encode_length_pos (message : PartyDetailsDefinitionRequestAck) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : PartyDetailsDefinitionRequestAck) : (encode message).length ≤ 6285 := by
  have bound_partyDetailsGroups := PartyDetailsGroups.encode_length_le message.partyDetailsGroups
  have bound_trdRegPublicationsGroups := TrdRegPublicationsGroups.encode_length_le message.trdRegPublicationsGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length, SelfMatchPreventionInstruction.encode_length, CmtaGiveupCd.encode_length, CustOrderHandlingInst.encode_length, ListUpdateAction.encode_length]
  omega

@[simp] theorem decode_encode (message : PartyDetailsDefinitionRequestAck) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [SelfMatchPreventionInstruction.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [CmtaGiveupCd.decode_encode]
  simp only [Option.bind_some]
  rw [CustOrderHandlingInst.decode_encode]
  simp only [Option.bind_some]
  rw [ListUpdateAction.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [PartyDetailsGroups.decode_encode]
  simp only [Option.bind_some]
  rw [TrdRegPublicationsGroups.decode_encode, Option.bind_some]
  rfl

end PartyDetailsDefinitionRequestAck

/-- Business Reject: 330 bytes -/
structure BusinessReject where
  seqNum : BitVec 32
  uuid : BitVec 64
  text : Alpha 256
  senderIdOptional : Alpha 20
  partyDetailsListReqIdOptional : BitVec 64
  sendingTimeEpoch : BitVec 64
  businessRejectRefId : BitVec 64
  locationOptional : Alpha 5
  refSeqNum : BitVec 32
  refTagId : BitVec 16
  businessRejectReason : BitVec 16
  refMsgType : Alpha 2
  possRetransFlag : BitVec 8
  manualOrderIndicatorOptional : BitVec 8
  splitMsg : BitVec 8
  deriving DecidableEq, Repr

namespace BusinessReject

def encode (message : BusinessReject) : List UInt8 :=
  encodeUIntLE 4 message.seqNum
    ++ encodeUIntLE 8 message.uuid
    ++ Alpha.encode message.text
    ++ Alpha.encode message.senderIdOptional
    ++ encodeUIntLE 8 message.partyDetailsListReqIdOptional
    ++ encodeUIntLE 8 message.sendingTimeEpoch
    ++ encodeUIntLE 8 message.businessRejectRefId
    ++ Alpha.encode message.locationOptional
    ++ encodeUIntLE 4 message.refSeqNum
    ++ encodeUIntLE 2 message.refTagId
    ++ encodeUIntLE 2 message.businessRejectReason
    ++ Alpha.encode message.refMsgType
    ++ encodeUInt 1 message.possRetransFlag
    ++ encodeUInt 1 message.manualOrderIndicatorOptional
    ++ encodeUInt 1 message.splitMsg

def decode (bytes : List UInt8) : Option (BusinessReject × List UInt8) := do
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (uuid, bytes) ← decodeUIntLE 8 bytes
  let (text, bytes) ← Alpha.decode 256 bytes
  let (senderIdOptional, bytes) ← Alpha.decode 20 bytes
  let (partyDetailsListReqIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (sendingTimeEpoch, bytes) ← decodeUIntLE 8 bytes
  let (businessRejectRefId, bytes) ← decodeUIntLE 8 bytes
  let (locationOptional, bytes) ← Alpha.decode 5 bytes
  let (refSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (refTagId, bytes) ← decodeUIntLE 2 bytes
  let (businessRejectReason, bytes) ← decodeUIntLE 2 bytes
  let (refMsgType, bytes) ← Alpha.decode 2 bytes
  let (possRetransFlag, bytes) ← decodeUInt 1 bytes
  let (manualOrderIndicatorOptional, bytes) ← decodeUInt 1 bytes
  let (splitMsg, bytes) ← decodeUInt 1 bytes
  pure ({ seqNum, uuid, text, senderIdOptional, partyDetailsListReqIdOptional, sendingTimeEpoch, businessRejectRefId, locationOptional, refSeqNum, refTagId, businessRejectReason, refMsgType, possRetransFlag, manualOrderIndicatorOptional, splitMsg }, bytes)

@[simp] theorem encode_length (message : BusinessReject) : (encode message).length = 330 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : BusinessReject) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BusinessReject) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end BusinessReject

/-- Execution Report New: 209 bytes -/
structure ExecutionReportNew where
  seqNum : BitVec 32
  uuid : BitVec 64
  execId : Alpha 40
  senderId : Alpha 20
  clordid : Alpha 20
  partyDetailsListReqId : BitVec 64
  orderId : BitVec 64
  price : BitVec 64
  stopPx : BitVec 64
  transactTime : BitVec 64
  sendingTimeEpoch : BitVec 64
  orderRequestId : BitVec 64
  crossIdOptional : BitVec 64
  hostCrossId : BitVec 64
  location : Alpha 5
  securityId : BitVec 32
  orderQty : BitVec 32
  minQty : BitVec 32
  displayQty : BitVec 32
  expireDate : BitVec 16
  delayDuration : BitVec 16
  ordTypeOptional : OrdTypeOptional
  side : BitVec 8
  timeInForce : BitVec 8
  manualOrderIndicator : BitVec 8
  possRetransFlag : BitVec 8
  splitMsg : BitVec 8
  crossType : BitVec 8
  execInst : BitVec 8
  executionMode : ExecutionMode
  liquidityFlag : BitVec 8
  managedOrder : BitVec 8
  shortSaleType : BitVec 8
  delayToTime : BitVec 64
  deriving DecidableEq, Repr

namespace ExecutionReportNew

def encode (message : ExecutionReportNew) : List UInt8 :=
  encodeUIntLE 4 message.seqNum
    ++ encodeUIntLE 8 message.uuid
    ++ Alpha.encode message.execId
    ++ Alpha.encode message.senderId
    ++ Alpha.encode message.clordid
    ++ encodeUIntLE 8 message.partyDetailsListReqId
    ++ encodeUIntLE 8 message.orderId
    ++ encodeUIntLE 8 message.price
    ++ encodeUIntLE 8 message.stopPx
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.sendingTimeEpoch
    ++ encodeUIntLE 8 message.orderRequestId
    ++ encodeUIntLE 8 message.crossIdOptional
    ++ encodeUIntLE 8 message.hostCrossId
    ++ Alpha.encode message.location
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 4 message.orderQty
    ++ encodeUIntLE 4 message.minQty
    ++ encodeUIntLE 4 message.displayQty
    ++ encodeUIntLE 2 message.expireDate
    ++ encodeUIntLE 2 message.delayDuration
    ++ OrdTypeOptional.encode message.ordTypeOptional
    ++ encodeUInt 1 message.side
    ++ encodeUInt 1 message.timeInForce
    ++ encodeUInt 1 message.manualOrderIndicator
    ++ encodeUInt 1 message.possRetransFlag
    ++ encodeUInt 1 message.splitMsg
    ++ encodeUInt 1 message.crossType
    ++ encodeUIntLE 1 message.execInst
    ++ ExecutionMode.encode message.executionMode
    ++ encodeUInt 1 message.liquidityFlag
    ++ encodeUInt 1 message.managedOrder
    ++ encodeUInt 1 message.shortSaleType
    ++ encodeUIntLE 8 message.delayToTime

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ExecutionReportNew × List UInt8) := do
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (uuid, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← Alpha.decode 40 bytes
  let (senderId, bytes) ← Alpha.decode 20 bytes
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (partyDetailsListReqId, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (stopPx, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (sendingTimeEpoch, bytes) ← decodeUIntLE 8 bytes
  let (orderRequestId, bytes) ← decodeUIntLE 8 bytes
  let (crossIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (hostCrossId, bytes) ← decodeUIntLE 8 bytes
  let (location, bytes) ← Alpha.decode 5 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (minQty, bytes) ← decodeUIntLE 4 bytes
  let (displayQty, bytes) ← decodeUIntLE 4 bytes
  let (expireDate, bytes) ← decodeUIntLE 2 bytes
  let (delayDuration, bytes) ← decodeUIntLE 2 bytes
  let (ordTypeOptional, bytes) ← OrdTypeOptional.decode bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (manualOrderIndicator, bytes) ← decodeUInt 1 bytes
  let (possRetransFlag, bytes) ← decodeUInt 1 bytes
  let (splitMsg, bytes) ← decodeUInt 1 bytes
  let (crossType, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUIntLE 1 bytes
  let (executionMode, bytes) ← ExecutionMode.decode bytes
  let (liquidityFlag, bytes) ← decodeUInt 1 bytes
  let (managedOrder, bytes) ← decodeUInt 1 bytes
  let (shortSaleType, bytes) ← decodeUInt 1 bytes
  let (delayToTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ seqNum, uuid, execId, senderId, clordid, partyDetailsListReqId, orderId, price, stopPx, transactTime, sendingTimeEpoch, orderRequestId, crossIdOptional, hostCrossId, location, securityId, orderQty, minQty, displayQty, expireDate, delayDuration, ordTypeOptional, side, timeInForce, manualOrderIndicator, possRetransFlag, splitMsg, crossType, execInst, executionMode, liquidityFlag, managedOrder, shortSaleType, delayToTime }, bytes)

@[simp] theorem encode_length (message : ExecutionReportNew) : (encode message).length = 209 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, OrdTypeOptional.encode_length, encodeUInt_length, ExecutionMode.encode_length]

theorem encode_length_pos (message : ExecutionReportNew) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutionReportNew) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [OrdTypeOptional.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [ExecutionMode.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end ExecutionReportNew

/-- Execution Report Reject: 467 bytes -/
structure ExecutionReportReject where
  seqNum : BitVec 32
  uuid : BitVec 64
  text : Alpha 256
  execId : Alpha 40
  senderId : Alpha 20
  clordid : Alpha 20
  partyDetailsListReqId : BitVec 64
  orderId : BitVec 64
  priceOptional : BitVec 64
  stopPx : BitVec 64
  transactTime : BitVec 64
  sendingTimeEpoch : BitVec 64
  orderRequestId : BitVec 64
  crossIdOptional : BitVec 64
  hostCrossId : BitVec 64
  location : Alpha 5
  securityId : BitVec 32
  orderQty : BitVec 32
  minQty : BitVec 32
  displayQty : BitVec 32
  ordRejReason : BitVec 16
  expireDate : BitVec 16
  delayDuration : BitVec 16
  ordTypeOptional : OrdTypeOptional
  side : BitVec 8
  timeInForce : BitVec 8
  manualOrderIndicator : BitVec 8
  possRetransFlag : BitVec 8
  splitMsg : BitVec 8
  crossType : BitVec 8
  execInst : BitVec 8
  executionMode : ExecutionMode
  liquidityFlag : BitVec 8
  managedOrder : BitVec 8
  shortSaleType : BitVec 8
  delayToTime : BitVec 64
  deriving DecidableEq, Repr

namespace ExecutionReportReject

def encode (message : ExecutionReportReject) : List UInt8 :=
  encodeUIntLE 4 message.seqNum
    ++ encodeUIntLE 8 message.uuid
    ++ Alpha.encode message.text
    ++ Alpha.encode message.execId
    ++ Alpha.encode message.senderId
    ++ Alpha.encode message.clordid
    ++ encodeUIntLE 8 message.partyDetailsListReqId
    ++ encodeUIntLE 8 message.orderId
    ++ encodeUIntLE 8 message.priceOptional
    ++ encodeUIntLE 8 message.stopPx
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.sendingTimeEpoch
    ++ encodeUIntLE 8 message.orderRequestId
    ++ encodeUIntLE 8 message.crossIdOptional
    ++ encodeUIntLE 8 message.hostCrossId
    ++ Alpha.encode message.location
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 4 message.orderQty
    ++ encodeUIntLE 4 message.minQty
    ++ encodeUIntLE 4 message.displayQty
    ++ encodeUIntLE 2 message.ordRejReason
    ++ encodeUIntLE 2 message.expireDate
    ++ encodeUIntLE 2 message.delayDuration
    ++ OrdTypeOptional.encode message.ordTypeOptional
    ++ encodeUInt 1 message.side
    ++ encodeUInt 1 message.timeInForce
    ++ encodeUInt 1 message.manualOrderIndicator
    ++ encodeUInt 1 message.possRetransFlag
    ++ encodeUInt 1 message.splitMsg
    ++ encodeUInt 1 message.crossType
    ++ encodeUIntLE 1 message.execInst
    ++ ExecutionMode.encode message.executionMode
    ++ encodeUInt 1 message.liquidityFlag
    ++ encodeUInt 1 message.managedOrder
    ++ encodeUInt 1 message.shortSaleType
    ++ encodeUIntLE 8 message.delayToTime

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ExecutionReportReject × List UInt8) := do
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (uuid, bytes) ← decodeUIntLE 8 bytes
  let (text, bytes) ← Alpha.decode 256 bytes
  let (execId, bytes) ← Alpha.decode 40 bytes
  let (senderId, bytes) ← Alpha.decode 20 bytes
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (partyDetailsListReqId, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (priceOptional, bytes) ← decodeUIntLE 8 bytes
  let (stopPx, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (sendingTimeEpoch, bytes) ← decodeUIntLE 8 bytes
  let (orderRequestId, bytes) ← decodeUIntLE 8 bytes
  let (crossIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (hostCrossId, bytes) ← decodeUIntLE 8 bytes
  let (location, bytes) ← Alpha.decode 5 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (minQty, bytes) ← decodeUIntLE 4 bytes
  let (displayQty, bytes) ← decodeUIntLE 4 bytes
  let (ordRejReason, bytes) ← decodeUIntLE 2 bytes
  let (expireDate, bytes) ← decodeUIntLE 2 bytes
  let (delayDuration, bytes) ← decodeUIntLE 2 bytes
  let (ordTypeOptional, bytes) ← OrdTypeOptional.decode bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (manualOrderIndicator, bytes) ← decodeUInt 1 bytes
  let (possRetransFlag, bytes) ← decodeUInt 1 bytes
  let (splitMsg, bytes) ← decodeUInt 1 bytes
  let (crossType, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUIntLE 1 bytes
  let (executionMode, bytes) ← ExecutionMode.decode bytes
  let (liquidityFlag, bytes) ← decodeUInt 1 bytes
  let (managedOrder, bytes) ← decodeUInt 1 bytes
  let (shortSaleType, bytes) ← decodeUInt 1 bytes
  let (delayToTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ seqNum, uuid, text, execId, senderId, clordid, partyDetailsListReqId, orderId, priceOptional, stopPx, transactTime, sendingTimeEpoch, orderRequestId, crossIdOptional, hostCrossId, location, securityId, orderQty, minQty, displayQty, ordRejReason, expireDate, delayDuration, ordTypeOptional, side, timeInForce, manualOrderIndicator, possRetransFlag, splitMsg, crossType, execInst, executionMode, liquidityFlag, managedOrder, shortSaleType, delayToTime }, bytes)

@[simp] theorem encode_length (message : ExecutionReportReject) : (encode message).length = 467 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, OrdTypeOptional.encode_length, encodeUInt_length, ExecutionMode.encode_length]

theorem encode_length_pos (message : ExecutionReportReject) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutionReportReject) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [OrdTypeOptional.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [ExecutionMode.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end ExecutionReportReject

/-- Execution Report Elimination: 202 bytes -/
structure ExecutionReportElimination where
  seqNum : BitVec 32
  uuid : BitVec 64
  execId : Alpha 40
  senderId : Alpha 20
  clordid : Alpha 20
  partyDetailsListReqId : BitVec 64
  orderId : BitVec 64
  price : BitVec 64
  stopPx : BitVec 64
  transactTime : BitVec 64
  sendingTimeEpoch : BitVec 64
  orderRequestId : BitVec 64
  crossIdOptional : BitVec 64
  hostCrossId : BitVec 64
  location : Alpha 5
  securityId : BitVec 32
  cumQty : BitVec 32
  orderQty : BitVec 32
  minQty : BitVec 32
  displayQty : BitVec 32
  expireDate : BitVec 16
  ordTypeOptional : OrdTypeOptional
  side : BitVec 8
  timeInForce : BitVec 8
  manualOrderIndicator : BitVec 8
  possRetransFlag : BitVec 8
  crossType : BitVec 8
  execInst : BitVec 8
  executionMode : ExecutionMode
  liquidityFlag : BitVec 8
  managedOrder : BitVec 8
  shortSaleType : BitVec 8
  deriving DecidableEq, Repr

namespace ExecutionReportElimination

def encode (message : ExecutionReportElimination) : List UInt8 :=
  encodeUIntLE 4 message.seqNum
    ++ encodeUIntLE 8 message.uuid
    ++ Alpha.encode message.execId
    ++ Alpha.encode message.senderId
    ++ Alpha.encode message.clordid
    ++ encodeUIntLE 8 message.partyDetailsListReqId
    ++ encodeUIntLE 8 message.orderId
    ++ encodeUIntLE 8 message.price
    ++ encodeUIntLE 8 message.stopPx
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.sendingTimeEpoch
    ++ encodeUIntLE 8 message.orderRequestId
    ++ encodeUIntLE 8 message.crossIdOptional
    ++ encodeUIntLE 8 message.hostCrossId
    ++ Alpha.encode message.location
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 4 message.cumQty
    ++ encodeUIntLE 4 message.orderQty
    ++ encodeUIntLE 4 message.minQty
    ++ encodeUIntLE 4 message.displayQty
    ++ encodeUIntLE 2 message.expireDate
    ++ OrdTypeOptional.encode message.ordTypeOptional
    ++ encodeUInt 1 message.side
    ++ encodeUInt 1 message.timeInForce
    ++ encodeUInt 1 message.manualOrderIndicator
    ++ encodeUInt 1 message.possRetransFlag
    ++ encodeUInt 1 message.crossType
    ++ encodeUIntLE 1 message.execInst
    ++ ExecutionMode.encode message.executionMode
    ++ encodeUInt 1 message.liquidityFlag
    ++ encodeUInt 1 message.managedOrder
    ++ encodeUInt 1 message.shortSaleType

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ExecutionReportElimination × List UInt8) := do
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (uuid, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← Alpha.decode 40 bytes
  let (senderId, bytes) ← Alpha.decode 20 bytes
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (partyDetailsListReqId, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (stopPx, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (sendingTimeEpoch, bytes) ← decodeUIntLE 8 bytes
  let (orderRequestId, bytes) ← decodeUIntLE 8 bytes
  let (crossIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (hostCrossId, bytes) ← decodeUIntLE 8 bytes
  let (location, bytes) ← Alpha.decode 5 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (cumQty, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (minQty, bytes) ← decodeUIntLE 4 bytes
  let (displayQty, bytes) ← decodeUIntLE 4 bytes
  let (expireDate, bytes) ← decodeUIntLE 2 bytes
  let (ordTypeOptional, bytes) ← OrdTypeOptional.decode bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (manualOrderIndicator, bytes) ← decodeUInt 1 bytes
  let (possRetransFlag, bytes) ← decodeUInt 1 bytes
  let (crossType, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUIntLE 1 bytes
  let (executionMode, bytes) ← ExecutionMode.decode bytes
  let (liquidityFlag, bytes) ← decodeUInt 1 bytes
  let (managedOrder, bytes) ← decodeUInt 1 bytes
  let (shortSaleType, bytes) ← decodeUInt 1 bytes
  pure ({ seqNum, uuid, execId, senderId, clordid, partyDetailsListReqId, orderId, price, stopPx, transactTime, sendingTimeEpoch, orderRequestId, crossIdOptional, hostCrossId, location, securityId, cumQty, orderQty, minQty, displayQty, expireDate, ordTypeOptional, side, timeInForce, manualOrderIndicator, possRetransFlag, crossType, execInst, executionMode, liquidityFlag, managedOrder, shortSaleType }, bytes)

@[simp] theorem encode_length (message : ExecutionReportElimination) : (encode message).length = 202 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, OrdTypeOptional.encode_length, encodeUInt_length, ExecutionMode.encode_length]

theorem encode_length_pos (message : ExecutionReportElimination) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutionReportElimination) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [OrdTypeOptional.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [ExecutionMode.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end ExecutionReportElimination

/-- Fills Group: 15 bytes -/
structure FillsGroup where
  fillPx : BitVec 64
  fillQty : BitVec 32
  fillExecId : Alpha 2
  fillYieldType : BitVec 8
  deriving DecidableEq, Repr

namespace FillsGroup

def encode (message : FillsGroup) : List UInt8 :=
  encodeUIntLE 8 message.fillPx
    ++ encodeUIntLE 4 message.fillQty
    ++ Alpha.encode message.fillExecId
    ++ encodeUInt 1 message.fillYieldType

def decode (bytes : List UInt8) : Option (FillsGroup × List UInt8) := do
  let (fillPx, bytes) ← decodeUIntLE 8 bytes
  let (fillQty, bytes) ← decodeUIntLE 4 bytes
  let (fillExecId, bytes) ← Alpha.decode 2 bytes
  let (fillYieldType, bytes) ← decodeUInt 1 bytes
  pure ({ fillPx, fillQty, fillExecId, fillYieldType }, bytes)

@[simp] theorem encode_length (message : FillsGroup) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : FillsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FillsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end FillsGroup

/-- Fills Groups -/
structure FillsGroups where
  blockLength : BitVec 16
  fillsGroup : Bounded 1 FillsGroup
  deriving DecidableEq, Repr

namespace FillsGroups

def encode (message : FillsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.fillsGroup.val.length)
    ++ encodeMany FillsGroup.encode message.fillsGroup.val

def decode (bytes : List UInt8) : Option (FillsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (fillsGroup_, bytes) ← decodeMany FillsGroup.decode numInGroup.toNat bytes
  if fits_fillsGroup : fillsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, fillsGroup := ⟨fillsGroup_, fits_fillsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : FillsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : FillsGroups) : (encode message).length ≤ 3828 := by
  have bound_fillsGroup := message.fillsGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const FillsGroup.encode 15 FillsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : FillsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 FillsGroup.encode FillsGroup.decode FillsGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.fillsGroup.length_lt, ↓reduceDIte]
  rfl

end FillsGroups

/-- Outright Order Events Group: 23 bytes -/
structure OutrightOrderEventsGroup where
  orderEventPx : BitVec 64
  orderEventText : Alpha 5
  orderEventExecId : BitVec 32
  orderEventQty : BitVec 32
  orderEventType : BitVec 8
  orderEventReason : BitVec 8
  deriving DecidableEq, Repr

namespace OutrightOrderEventsGroup

def encode (message : OutrightOrderEventsGroup) : List UInt8 :=
  encodeUIntLE 8 message.orderEventPx
    ++ Alpha.encode message.orderEventText
    ++ encodeUIntLE 4 message.orderEventExecId
    ++ encodeUIntLE 4 message.orderEventQty
    ++ encodeUInt 1 message.orderEventType
    ++ encodeUInt 1 message.orderEventReason

def decode (bytes : List UInt8) : Option (OutrightOrderEventsGroup × List UInt8) := do
  let (orderEventPx, bytes) ← decodeUIntLE 8 bytes
  let (orderEventText, bytes) ← Alpha.decode 5 bytes
  let (orderEventExecId, bytes) ← decodeUIntLE 4 bytes
  let (orderEventQty, bytes) ← decodeUIntLE 4 bytes
  let (orderEventType, bytes) ← decodeUInt 1 bytes
  let (orderEventReason, bytes) ← decodeUInt 1 bytes
  pure ({ orderEventPx, orderEventText, orderEventExecId, orderEventQty, orderEventType, orderEventReason }, bytes)

@[simp] theorem encode_length (message : OutrightOrderEventsGroup) : (encode message).length = 23 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : OutrightOrderEventsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OutrightOrderEventsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end OutrightOrderEventsGroup

/-- Outright Order Events Groups -/
structure OutrightOrderEventsGroups where
  blockLength : BitVec 16
  outrightOrderEventsGroup : Bounded 1 OutrightOrderEventsGroup
  deriving DecidableEq, Repr

namespace OutrightOrderEventsGroups

def encode (message : OutrightOrderEventsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.outrightOrderEventsGroup.val.length)
    ++ encodeMany OutrightOrderEventsGroup.encode message.outrightOrderEventsGroup.val

def decode (bytes : List UInt8) : Option (OutrightOrderEventsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (outrightOrderEventsGroup_, bytes) ← decodeMany OutrightOrderEventsGroup.decode numInGroup.toNat bytes
  if fits_outrightOrderEventsGroup : outrightOrderEventsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, outrightOrderEventsGroup := ⟨outrightOrderEventsGroup_, fits_outrightOrderEventsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : OutrightOrderEventsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OutrightOrderEventsGroups) : (encode message).length ≤ 5868 := by
  have bound_outrightOrderEventsGroup := message.outrightOrderEventsGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const OutrightOrderEventsGroup.encode 23 OutrightOrderEventsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : OutrightOrderEventsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 OutrightOrderEventsGroup.encode OutrightOrderEventsGroup.decode OutrightOrderEventsGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.outrightOrderEventsGroup.length_lt, ↓reduceDIte]
  rfl

end OutrightOrderEventsGroups

/-- Execution Report Trade Outright -/
structure ExecutionReportTradeOutright where
  seqNum : BitVec 32
  uuid : BitVec 64
  execId : Alpha 40
  senderId : Alpha 20
  clordid : Alpha 20
  partyDetailsListReqId : BitVec 64
  lastPx : BitVec 64
  orderId : BitVec 64
  price : BitVec 64
  stopPx : BitVec 64
  transactTime : BitVec 64
  sendingTimeEpoch : BitVec 64
  orderRequestId : BitVec 64
  secExecId : BitVec 64
  crossIdOptional : BitVec 64
  hostCrossId : BitVec 64
  location : Alpha 5
  securityId : BitVec 32
  orderQty : BitVec 32
  lastQty : BitVec 32
  cumQty : BitVec 32
  mdTradeEntryId : BitVec 32
  sideTradeId : BitVec 32
  tradeLinkId : BitVec 32
  leavesQty : BitVec 32
  tradeDate : BitVec 16
  expireDate : BitVec 16
  ordStatusTrd : BitVec 8
  ordTypeOptional : OrdTypeOptional
  side : BitVec 8
  timeInForce : BitVec 8
  manualOrderIndicator : BitVec 8
  possRetransFlag : BitVec 8
  aggressorIndicator : BitVec 8
  crossType : BitVec 8
  execInst : BitVec 8
  executionMode : ExecutionMode
  liquidityFlag : BitVec 8
  managedOrder : BitVec 8
  shortSaleType : BitVec 8
  ownership : BitVec 8
  fillsGroups : FillsGroups
  outrightOrderEventsGroups : OutrightOrderEventsGroups
  deriving DecidableEq, Repr

namespace ExecutionReportTradeOutright

def encode (message : ExecutionReportTradeOutright) : List UInt8 :=
  encodeUIntLE 4 message.seqNum
    ++ encodeUIntLE 8 message.uuid
    ++ Alpha.encode message.execId
    ++ Alpha.encode message.senderId
    ++ Alpha.encode message.clordid
    ++ encodeUIntLE 8 message.partyDetailsListReqId
    ++ encodeUIntLE 8 message.lastPx
    ++ encodeUIntLE 8 message.orderId
    ++ encodeUIntLE 8 message.price
    ++ encodeUIntLE 8 message.stopPx
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.sendingTimeEpoch
    ++ encodeUIntLE 8 message.orderRequestId
    ++ encodeUIntLE 8 message.secExecId
    ++ encodeUIntLE 8 message.crossIdOptional
    ++ encodeUIntLE 8 message.hostCrossId
    ++ Alpha.encode message.location
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 4 message.orderQty
    ++ encodeUIntLE 4 message.lastQty
    ++ encodeUIntLE 4 message.cumQty
    ++ encodeUIntLE 4 message.mdTradeEntryId
    ++ encodeUIntLE 4 message.sideTradeId
    ++ encodeUIntLE 4 message.tradeLinkId
    ++ encodeUIntLE 4 message.leavesQty
    ++ encodeUIntLE 2 message.tradeDate
    ++ encodeUIntLE 2 message.expireDate
    ++ encodeUInt 1 message.ordStatusTrd
    ++ OrdTypeOptional.encode message.ordTypeOptional
    ++ encodeUInt 1 message.side
    ++ encodeUInt 1 message.timeInForce
    ++ encodeUInt 1 message.manualOrderIndicator
    ++ encodeUInt 1 message.possRetransFlag
    ++ encodeUInt 1 message.aggressorIndicator
    ++ encodeUInt 1 message.crossType
    ++ encodeUIntLE 1 message.execInst
    ++ ExecutionMode.encode message.executionMode
    ++ encodeUInt 1 message.liquidityFlag
    ++ encodeUInt 1 message.managedOrder
    ++ encodeUInt 1 message.shortSaleType
    ++ encodeUInt 1 message.ownership
    ++ FillsGroups.encode message.fillsGroups
    ++ OutrightOrderEventsGroups.encode message.outrightOrderEventsGroups

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ExecutionReportTradeOutright × List UInt8) := do
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (uuid, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← Alpha.decode 40 bytes
  let (senderId, bytes) ← Alpha.decode 20 bytes
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (partyDetailsListReqId, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (stopPx, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (sendingTimeEpoch, bytes) ← decodeUIntLE 8 bytes
  let (orderRequestId, bytes) ← decodeUIntLE 8 bytes
  let (secExecId, bytes) ← decodeUIntLE 8 bytes
  let (crossIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (hostCrossId, bytes) ← decodeUIntLE 8 bytes
  let (location, bytes) ← Alpha.decode 5 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (cumQty, bytes) ← decodeUIntLE 4 bytes
  let (mdTradeEntryId, bytes) ← decodeUIntLE 4 bytes
  let (sideTradeId, bytes) ← decodeUIntLE 4 bytes
  let (tradeLinkId, bytes) ← decodeUIntLE 4 bytes
  let (leavesQty, bytes) ← decodeUIntLE 4 bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (expireDate, bytes) ← decodeUIntLE 2 bytes
  let (ordStatusTrd, bytes) ← decodeUInt 1 bytes
  let (ordTypeOptional, bytes) ← OrdTypeOptional.decode bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (manualOrderIndicator, bytes) ← decodeUInt 1 bytes
  let (possRetransFlag, bytes) ← decodeUInt 1 bytes
  let (aggressorIndicator, bytes) ← decodeUInt 1 bytes
  let (crossType, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUIntLE 1 bytes
  let (executionMode, bytes) ← ExecutionMode.decode bytes
  let (liquidityFlag, bytes) ← decodeUInt 1 bytes
  let (managedOrder, bytes) ← decodeUInt 1 bytes
  let (shortSaleType, bytes) ← decodeUInt 1 bytes
  let (ownership, bytes) ← decodeUInt 1 bytes
  let (fillsGroups, bytes) ← FillsGroups.decode bytes
  let (outrightOrderEventsGroups, bytes) ← OutrightOrderEventsGroups.decode bytes
  pure ({ seqNum, uuid, execId, senderId, clordid, partyDetailsListReqId, lastPx, orderId, price, stopPx, transactTime, sendingTimeEpoch, orderRequestId, secExecId, crossIdOptional, hostCrossId, location, securityId, orderQty, lastQty, cumQty, mdTradeEntryId, sideTradeId, tradeLinkId, leavesQty, tradeDate, expireDate, ordStatusTrd, ordTypeOptional, side, timeInForce, manualOrderIndicator, possRetransFlag, aggressorIndicator, crossType, execInst, executionMode, liquidityFlag, managedOrder, shortSaleType, ownership, fillsGroups, outrightOrderEventsGroups }, bytes)

theorem encode_length_pos (message : ExecutionReportTradeOutright) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ExecutionReportTradeOutright) : (encode message).length ≤ 9931 := by
  have bound_fillsGroups := FillsGroups.encode_length_le message.fillsGroups
  have bound_outrightOrderEventsGroups := OutrightOrderEventsGroups.encode_length_le message.outrightOrderEventsGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length, OrdTypeOptional.encode_length, ExecutionMode.encode_length]
  omega

@[simp] theorem decode_encode (message : ExecutionReportTradeOutright) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [OrdTypeOptional.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [ExecutionMode.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [FillsGroups.decode_encode]
  simp only [Option.bind_some]
  rw [OutrightOrderEventsGroups.decode_encode, Option.bind_some]
  rfl

end ExecutionReportTradeOutright

/-- Trade Legs Group: 29 bytes -/
structure TradeLegsGroup where
  legExecId : BitVec 64
  legLastPx : BitVec 64
  legSecurityId : BitVec 32
  legTradeId : BitVec 32
  legLastQty : BitVec 32
  legSide : BitVec 8
  deriving DecidableEq, Repr

namespace TradeLegsGroup

def encode (message : TradeLegsGroup) : List UInt8 :=
  encodeUIntLE 8 message.legExecId
    ++ encodeUIntLE 8 message.legLastPx
    ++ encodeUIntLE 4 message.legSecurityId
    ++ encodeUIntLE 4 message.legTradeId
    ++ encodeUIntLE 4 message.legLastQty
    ++ encodeUInt 1 message.legSide

def decode (bytes : List UInt8) : Option (TradeLegsGroup × List UInt8) := do
  let (legExecId, bytes) ← decodeUIntLE 8 bytes
  let (legLastPx, bytes) ← decodeUIntLE 8 bytes
  let (legSecurityId, bytes) ← decodeUIntLE 4 bytes
  let (legTradeId, bytes) ← decodeUIntLE 4 bytes
  let (legLastQty, bytes) ← decodeUIntLE 4 bytes
  let (legSide, bytes) ← decodeUInt 1 bytes
  pure ({ legExecId, legLastPx, legSecurityId, legTradeId, legLastQty, legSide }, bytes)

@[simp] theorem encode_length (message : TradeLegsGroup) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : TradeLegsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeLegsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end TradeLegsGroup

/-- Trade Legs Groups -/
structure TradeLegsGroups where
  blockLength : BitVec 16
  tradeLegsGroup : Bounded 1 TradeLegsGroup
  deriving DecidableEq, Repr

namespace TradeLegsGroups

def encode (message : TradeLegsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.tradeLegsGroup.val.length)
    ++ encodeMany TradeLegsGroup.encode message.tradeLegsGroup.val

def decode (bytes : List UInt8) : Option (TradeLegsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (tradeLegsGroup_, bytes) ← decodeMany TradeLegsGroup.decode numInGroup.toNat bytes
  if fits_tradeLegsGroup : tradeLegsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, tradeLegsGroup := ⟨tradeLegsGroup_, fits_tradeLegsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : TradeLegsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TradeLegsGroups) : (encode message).length ≤ 7398 := by
  have bound_tradeLegsGroup := message.tradeLegsGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const TradeLegsGroup.encode 29 TradeLegsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : TradeLegsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 TradeLegsGroup.encode TradeLegsGroup.decode TradeLegsGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.tradeLegsGroup.length_lt, ↓reduceDIte]
  rfl

end TradeLegsGroups

/-- Spread Order Events Group: 23 bytes -/
structure SpreadOrderEventsGroup where
  orderEventPx : BitVec 64
  orderEventText : Alpha 5
  orderEventExecId : BitVec 32
  orderEventQty : BitVec 32
  orderEventType : BitVec 8
  orderEventReason : BitVec 8
  deriving DecidableEq, Repr

namespace SpreadOrderEventsGroup

def encode (message : SpreadOrderEventsGroup) : List UInt8 :=
  encodeUIntLE 8 message.orderEventPx
    ++ Alpha.encode message.orderEventText
    ++ encodeUIntLE 4 message.orderEventExecId
    ++ encodeUIntLE 4 message.orderEventQty
    ++ encodeUInt 1 message.orderEventType
    ++ encodeUInt 1 message.orderEventReason

def decode (bytes : List UInt8) : Option (SpreadOrderEventsGroup × List UInt8) := do
  let (orderEventPx, bytes) ← decodeUIntLE 8 bytes
  let (orderEventText, bytes) ← Alpha.decode 5 bytes
  let (orderEventExecId, bytes) ← decodeUIntLE 4 bytes
  let (orderEventQty, bytes) ← decodeUIntLE 4 bytes
  let (orderEventType, bytes) ← decodeUInt 1 bytes
  let (orderEventReason, bytes) ← decodeUInt 1 bytes
  pure ({ orderEventPx, orderEventText, orderEventExecId, orderEventQty, orderEventType, orderEventReason }, bytes)

@[simp] theorem encode_length (message : SpreadOrderEventsGroup) : (encode message).length = 23 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SpreadOrderEventsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SpreadOrderEventsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end SpreadOrderEventsGroup

/-- Spread Order Events Groups -/
structure SpreadOrderEventsGroups where
  blockLength : BitVec 16
  spreadOrderEventsGroup : Bounded 1 SpreadOrderEventsGroup
  deriving DecidableEq, Repr

namespace SpreadOrderEventsGroups

def encode (message : SpreadOrderEventsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.spreadOrderEventsGroup.val.length)
    ++ encodeMany SpreadOrderEventsGroup.encode message.spreadOrderEventsGroup.val

def decode (bytes : List UInt8) : Option (SpreadOrderEventsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (spreadOrderEventsGroup_, bytes) ← decodeMany SpreadOrderEventsGroup.decode numInGroup.toNat bytes
  if fits_spreadOrderEventsGroup : spreadOrderEventsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, spreadOrderEventsGroup := ⟨spreadOrderEventsGroup_, fits_spreadOrderEventsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : SpreadOrderEventsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SpreadOrderEventsGroups) : (encode message).length ≤ 5868 := by
  have bound_spreadOrderEventsGroup := message.spreadOrderEventsGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const SpreadOrderEventsGroup.encode 23 SpreadOrderEventsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : SpreadOrderEventsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 SpreadOrderEventsGroup.encode SpreadOrderEventsGroup.decode SpreadOrderEventsGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.spreadOrderEventsGroup.length_lt, ↓reduceDIte]
  rfl

end SpreadOrderEventsGroups

/-- Execution Report Trade Spread -/
structure ExecutionReportTradeSpread where
  seqNum : BitVec 32
  uuid : BitVec 64
  execId : Alpha 40
  senderId : Alpha 20
  clordid : Alpha 20
  partyDetailsListReqId : BitVec 64
  lastPx : BitVec 64
  orderId : BitVec 64
  price : BitVec 64
  stopPx : BitVec 64
  transactTime : BitVec 64
  sendingTimeEpoch : BitVec 64
  orderRequestId : BitVec 64
  secExecId : BitVec 64
  crossIdOptional : BitVec 64
  hostCrossId : BitVec 64
  location : Alpha 5
  securityId : BitVec 32
  orderQty : BitVec 32
  lastQty : BitVec 32
  cumQty : BitVec 32
  mdTradeEntryId : BitVec 32
  sideTradeId : BitVec 32
  leavesQty : BitVec 32
  tradeDate : BitVec 16
  expireDate : BitVec 16
  ordStatusTrd : BitVec 8
  ordTypeOptional : OrdTypeOptional
  side : BitVec 8
  timeInForce : BitVec 8
  manualOrderIndicator : BitVec 8
  possRetransFlag : BitVec 8
  aggressorIndicator : BitVec 8
  crossType : BitVec 8
  totalNumSecurities : BitVec 8
  execInst : BitVec 8
  executionMode : ExecutionMode
  liquidityFlag : BitVec 8
  shortSaleType : BitVec 8
  fillsGroups : FillsGroups
  tradeLegsGroups : TradeLegsGroups
  spreadOrderEventsGroups : SpreadOrderEventsGroups
  deriving DecidableEq, Repr

namespace ExecutionReportTradeSpread

def encode (message : ExecutionReportTradeSpread) : List UInt8 :=
  encodeUIntLE 4 message.seqNum
    ++ encodeUIntLE 8 message.uuid
    ++ Alpha.encode message.execId
    ++ Alpha.encode message.senderId
    ++ Alpha.encode message.clordid
    ++ encodeUIntLE 8 message.partyDetailsListReqId
    ++ encodeUIntLE 8 message.lastPx
    ++ encodeUIntLE 8 message.orderId
    ++ encodeUIntLE 8 message.price
    ++ encodeUIntLE 8 message.stopPx
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.sendingTimeEpoch
    ++ encodeUIntLE 8 message.orderRequestId
    ++ encodeUIntLE 8 message.secExecId
    ++ encodeUIntLE 8 message.crossIdOptional
    ++ encodeUIntLE 8 message.hostCrossId
    ++ Alpha.encode message.location
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 4 message.orderQty
    ++ encodeUIntLE 4 message.lastQty
    ++ encodeUIntLE 4 message.cumQty
    ++ encodeUIntLE 4 message.mdTradeEntryId
    ++ encodeUIntLE 4 message.sideTradeId
    ++ encodeUIntLE 4 message.leavesQty
    ++ encodeUIntLE 2 message.tradeDate
    ++ encodeUIntLE 2 message.expireDate
    ++ encodeUInt 1 message.ordStatusTrd
    ++ OrdTypeOptional.encode message.ordTypeOptional
    ++ encodeUInt 1 message.side
    ++ encodeUInt 1 message.timeInForce
    ++ encodeUInt 1 message.manualOrderIndicator
    ++ encodeUInt 1 message.possRetransFlag
    ++ encodeUInt 1 message.aggressorIndicator
    ++ encodeUInt 1 message.crossType
    ++ encodeUInt 1 message.totalNumSecurities
    ++ encodeUIntLE 1 message.execInst
    ++ ExecutionMode.encode message.executionMode
    ++ encodeUInt 1 message.liquidityFlag
    ++ encodeUInt 1 message.shortSaleType
    ++ FillsGroups.encode message.fillsGroups
    ++ TradeLegsGroups.encode message.tradeLegsGroups
    ++ SpreadOrderEventsGroups.encode message.spreadOrderEventsGroups

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ExecutionReportTradeSpread × List UInt8) := do
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (uuid, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← Alpha.decode 40 bytes
  let (senderId, bytes) ← Alpha.decode 20 bytes
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (partyDetailsListReqId, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (stopPx, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (sendingTimeEpoch, bytes) ← decodeUIntLE 8 bytes
  let (orderRequestId, bytes) ← decodeUIntLE 8 bytes
  let (secExecId, bytes) ← decodeUIntLE 8 bytes
  let (crossIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (hostCrossId, bytes) ← decodeUIntLE 8 bytes
  let (location, bytes) ← Alpha.decode 5 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (cumQty, bytes) ← decodeUIntLE 4 bytes
  let (mdTradeEntryId, bytes) ← decodeUIntLE 4 bytes
  let (sideTradeId, bytes) ← decodeUIntLE 4 bytes
  let (leavesQty, bytes) ← decodeUIntLE 4 bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (expireDate, bytes) ← decodeUIntLE 2 bytes
  let (ordStatusTrd, bytes) ← decodeUInt 1 bytes
  let (ordTypeOptional, bytes) ← OrdTypeOptional.decode bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (manualOrderIndicator, bytes) ← decodeUInt 1 bytes
  let (possRetransFlag, bytes) ← decodeUInt 1 bytes
  let (aggressorIndicator, bytes) ← decodeUInt 1 bytes
  let (crossType, bytes) ← decodeUInt 1 bytes
  let (totalNumSecurities, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUIntLE 1 bytes
  let (executionMode, bytes) ← ExecutionMode.decode bytes
  let (liquidityFlag, bytes) ← decodeUInt 1 bytes
  let (shortSaleType, bytes) ← decodeUInt 1 bytes
  let (fillsGroups, bytes) ← FillsGroups.decode bytes
  let (tradeLegsGroups, bytes) ← TradeLegsGroups.decode bytes
  let (spreadOrderEventsGroups, bytes) ← SpreadOrderEventsGroups.decode bytes
  pure ({ seqNum, uuid, execId, senderId, clordid, partyDetailsListReqId, lastPx, orderId, price, stopPx, transactTime, sendingTimeEpoch, orderRequestId, secExecId, crossIdOptional, hostCrossId, location, securityId, orderQty, lastQty, cumQty, mdTradeEntryId, sideTradeId, leavesQty, tradeDate, expireDate, ordStatusTrd, ordTypeOptional, side, timeInForce, manualOrderIndicator, possRetransFlag, aggressorIndicator, crossType, totalNumSecurities, execInst, executionMode, liquidityFlag, shortSaleType, fillsGroups, tradeLegsGroups, spreadOrderEventsGroups }, bytes)

theorem encode_length_pos (message : ExecutionReportTradeSpread) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ExecutionReportTradeSpread) : (encode message).length ≤ 17324 := by
  have bound_fillsGroups := FillsGroups.encode_length_le message.fillsGroups
  have bound_tradeLegsGroups := TradeLegsGroups.encode_length_le message.tradeLegsGroups
  have bound_spreadOrderEventsGroups := SpreadOrderEventsGroups.encode_length_le message.spreadOrderEventsGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length, OrdTypeOptional.encode_length, ExecutionMode.encode_length]
  omega

@[simp] theorem decode_encode (message : ExecutionReportTradeSpread) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [OrdTypeOptional.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [ExecutionMode.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [FillsGroups.decode_encode]
  simp only [Option.bind_some]
  rw [TradeLegsGroups.decode_encode]
  simp only [Option.bind_some]
  rw [SpreadOrderEventsGroups.decode_encode, Option.bind_some]
  rfl

end ExecutionReportTradeSpread

/-- Volatility: 9 bytes -/
structure Volatility where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace Volatility

def encode (message : Volatility) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (Volatility × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : Volatility) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : Volatility) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Volatility) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end Volatility

/-- Option Delta: 5 bytes -/
structure OptionDelta where
  mantissa32 : BitVec 32
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace OptionDelta

def encode (message : OptionDelta) : List UInt8 :=
  encodeUIntLE 4 message.mantissa32
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (OptionDelta × List UInt8) := do
  let (mantissa32, bytes) ← decodeUIntLE 4 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa32, exponent }, bytes)

@[simp] theorem encode_length (message : OptionDelta) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : OptionDelta) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OptionDelta) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end OptionDelta

/-- Time To Expiration: 5 bytes -/
structure TimeToExpiration where
  mantissa32 : BitVec 32
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace TimeToExpiration

def encode (message : TimeToExpiration) : List UInt8 :=
  encodeUIntLE 4 message.mantissa32
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (TimeToExpiration × List UInt8) := do
  let (mantissa32, bytes) ← decodeUIntLE 4 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa32, exponent }, bytes)

@[simp] theorem encode_length (message : TimeToExpiration) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : TimeToExpiration) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TimeToExpiration) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end TimeToExpiration

/-- Risk Free Rate: 5 bytes -/
structure RiskFreeRate where
  mantissa32 : BitVec 32
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace RiskFreeRate

def encode (message : RiskFreeRate) : List UInt8 :=
  encodeUIntLE 4 message.mantissa32
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (RiskFreeRate × List UInt8) := do
  let (mantissa32, bytes) ← decodeUIntLE 4 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa32, exponent }, bytes)

@[simp] theorem encode_length (message : RiskFreeRate) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : RiskFreeRate) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RiskFreeRate) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end RiskFreeRate

/-- Spread Leg Order Events Group: 23 bytes -/
structure SpreadLegOrderEventsGroup where
  orderEventPx : BitVec 64
  orderEventText : Alpha 5
  orderEventExecId : BitVec 32
  orderEventQty : BitVec 32
  orderEventType : BitVec 8
  orderEventReason : BitVec 8
  deriving DecidableEq, Repr

namespace SpreadLegOrderEventsGroup

def encode (message : SpreadLegOrderEventsGroup) : List UInt8 :=
  encodeUIntLE 8 message.orderEventPx
    ++ Alpha.encode message.orderEventText
    ++ encodeUIntLE 4 message.orderEventExecId
    ++ encodeUIntLE 4 message.orderEventQty
    ++ encodeUInt 1 message.orderEventType
    ++ encodeUInt 1 message.orderEventReason

def decode (bytes : List UInt8) : Option (SpreadLegOrderEventsGroup × List UInt8) := do
  let (orderEventPx, bytes) ← decodeUIntLE 8 bytes
  let (orderEventText, bytes) ← Alpha.decode 5 bytes
  let (orderEventExecId, bytes) ← decodeUIntLE 4 bytes
  let (orderEventQty, bytes) ← decodeUIntLE 4 bytes
  let (orderEventType, bytes) ← decodeUInt 1 bytes
  let (orderEventReason, bytes) ← decodeUInt 1 bytes
  pure ({ orderEventPx, orderEventText, orderEventExecId, orderEventQty, orderEventType, orderEventReason }, bytes)

@[simp] theorem encode_length (message : SpreadLegOrderEventsGroup) : (encode message).length = 23 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SpreadLegOrderEventsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SpreadLegOrderEventsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end SpreadLegOrderEventsGroup

/-- Spread Leg Order Events Groups -/
structure SpreadLegOrderEventsGroups where
  blockLength : BitVec 16
  spreadLegOrderEventsGroup : Bounded 1 SpreadLegOrderEventsGroup
  deriving DecidableEq, Repr

namespace SpreadLegOrderEventsGroups

def encode (message : SpreadLegOrderEventsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.spreadLegOrderEventsGroup.val.length)
    ++ encodeMany SpreadLegOrderEventsGroup.encode message.spreadLegOrderEventsGroup.val

def decode (bytes : List UInt8) : Option (SpreadLegOrderEventsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (spreadLegOrderEventsGroup_, bytes) ← decodeMany SpreadLegOrderEventsGroup.decode numInGroup.toNat bytes
  if fits_spreadLegOrderEventsGroup : spreadLegOrderEventsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, spreadLegOrderEventsGroup := ⟨spreadLegOrderEventsGroup_, fits_spreadLegOrderEventsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : SpreadLegOrderEventsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SpreadLegOrderEventsGroups) : (encode message).length ≤ 5868 := by
  have bound_spreadLegOrderEventsGroup := message.spreadLegOrderEventsGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const SpreadLegOrderEventsGroup.encode 23 SpreadLegOrderEventsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : SpreadLegOrderEventsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 SpreadLegOrderEventsGroup.encode SpreadLegOrderEventsGroup.decode SpreadLegOrderEventsGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.spreadLegOrderEventsGroup.length_lt, ↓reduceDIte]
  rfl

end SpreadLegOrderEventsGroups

/-- Execution Report Trade Spread Leg -/
structure ExecutionReportTradeSpreadLeg where
  seqNum : BitVec 32
  uuid : BitVec 64
  execId : Alpha 40
  senderId : Alpha 20
  clordid : Alpha 20
  volatility : Volatility
  partyDetailsListReqId : BitVec 64
  lastPx : BitVec 64
  orderId : BitVec 64
  underlyingPx : BitVec 64
  transactTime : BitVec 64
  sendingTimeEpoch : BitVec 64
  secExecId : BitVec 64
  location : Alpha 5
  optionDelta : OptionDelta
  timeToExpiration : TimeToExpiration
  riskFreeRate : RiskFreeRate
  securityId : BitVec 32
  lastQty : BitVec 32
  cumQty : BitVec 32
  sideTradeId : BitVec 32
  tradeDate : BitVec 16
  ordStatusTrd : BitVec 8
  ordTypeOptional : OrdTypeOptional
  side : BitVec 8
  possRetransFlag : BitVec 8
  fillsGroups : FillsGroups
  spreadLegOrderEventsGroups : SpreadLegOrderEventsGroups
  deriving DecidableEq, Repr

namespace ExecutionReportTradeSpreadLeg

def encode (message : ExecutionReportTradeSpreadLeg) : List UInt8 :=
  encodeUIntLE 4 message.seqNum
    ++ encodeUIntLE 8 message.uuid
    ++ Alpha.encode message.execId
    ++ Alpha.encode message.senderId
    ++ Alpha.encode message.clordid
    ++ Volatility.encode message.volatility
    ++ encodeUIntLE 8 message.partyDetailsListReqId
    ++ encodeUIntLE 8 message.lastPx
    ++ encodeUIntLE 8 message.orderId
    ++ encodeUIntLE 8 message.underlyingPx
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.sendingTimeEpoch
    ++ encodeUIntLE 8 message.secExecId
    ++ Alpha.encode message.location
    ++ OptionDelta.encode message.optionDelta
    ++ TimeToExpiration.encode message.timeToExpiration
    ++ RiskFreeRate.encode message.riskFreeRate
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 4 message.lastQty
    ++ encodeUIntLE 4 message.cumQty
    ++ encodeUIntLE 4 message.sideTradeId
    ++ encodeUIntLE 2 message.tradeDate
    ++ encodeUInt 1 message.ordStatusTrd
    ++ OrdTypeOptional.encode message.ordTypeOptional
    ++ encodeUInt 1 message.side
    ++ encodeUInt 1 message.possRetransFlag
    ++ FillsGroups.encode message.fillsGroups
    ++ SpreadLegOrderEventsGroups.encode message.spreadLegOrderEventsGroups

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ExecutionReportTradeSpreadLeg × List UInt8) := do
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (uuid, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← Alpha.decode 40 bytes
  let (senderId, bytes) ← Alpha.decode 20 bytes
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (volatility, bytes) ← Volatility.decode bytes
  let (partyDetailsListReqId, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (underlyingPx, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (sendingTimeEpoch, bytes) ← decodeUIntLE 8 bytes
  let (secExecId, bytes) ← decodeUIntLE 8 bytes
  let (location, bytes) ← Alpha.decode 5 bytes
  let (optionDelta, bytes) ← OptionDelta.decode bytes
  let (timeToExpiration, bytes) ← TimeToExpiration.decode bytes
  let (riskFreeRate, bytes) ← RiskFreeRate.decode bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (cumQty, bytes) ← decodeUIntLE 4 bytes
  let (sideTradeId, bytes) ← decodeUIntLE 4 bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (ordStatusTrd, bytes) ← decodeUInt 1 bytes
  let (ordTypeOptional, bytes) ← OrdTypeOptional.decode bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (possRetransFlag, bytes) ← decodeUInt 1 bytes
  let (fillsGroups, bytes) ← FillsGroups.decode bytes
  let (spreadLegOrderEventsGroups, bytes) ← SpreadLegOrderEventsGroups.decode bytes
  pure ({ seqNum, uuid, execId, senderId, clordid, volatility, partyDetailsListReqId, lastPx, orderId, underlyingPx, transactTime, sendingTimeEpoch, secExecId, location, optionDelta, timeToExpiration, riskFreeRate, securityId, lastQty, cumQty, sideTradeId, tradeDate, ordStatusTrd, ordTypeOptional, side, possRetransFlag, fillsGroups, spreadLegOrderEventsGroups }, bytes)

theorem encode_length_pos (message : ExecutionReportTradeSpreadLeg) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ExecutionReportTradeSpreadLeg) : (encode message).length ≤ 9895 := by
  have bound_fillsGroups := FillsGroups.encode_length_le message.fillsGroups
  have bound_spreadLegOrderEventsGroups := SpreadLegOrderEventsGroups.encode_length_le message.spreadLegOrderEventsGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, Volatility.encode_length, OptionDelta.encode_length, TimeToExpiration.encode_length, RiskFreeRate.encode_length, encodeUInt_length, OrdTypeOptional.encode_length]
  omega

@[simp] theorem decode_encode (message : ExecutionReportTradeSpreadLeg) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Volatility.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [OptionDelta.decode_encode]
  simp only [Option.bind_some]
  rw [TimeToExpiration.decode_encode]
  simp only [Option.bind_some]
  rw [RiskFreeRate.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [OrdTypeOptional.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [FillsGroups.decode_encode]
  simp only [Option.bind_some]
  rw [SpreadLegOrderEventsGroups.decode_encode, Option.bind_some]
  rfl

end ExecutionReportTradeSpreadLeg

/-- Execution Report Modify: 217 bytes -/
structure ExecutionReportModify where
  seqNum : BitVec 32
  uuid : BitVec 64
  execId : Alpha 40
  senderId : Alpha 20
  clordid : Alpha 20
  partyDetailsListReqId : BitVec 64
  orderId : BitVec 64
  price : BitVec 64
  stopPx : BitVec 64
  transactTime : BitVec 64
  sendingTimeEpoch : BitVec 64
  orderRequestId : BitVec 64
  crossIdOptional : BitVec 64
  hostCrossId : BitVec 64
  location : Alpha 5
  securityId : BitVec 32
  orderQty : BitVec 32
  cumQty : BitVec 32
  leavesQty : BitVec 32
  minQty : BitVec 32
  displayQty : BitVec 32
  expireDate : BitVec 16
  delayDuration : BitVec 16
  ordTypeOptional : OrdTypeOptional
  side : BitVec 8
  timeInForce : BitVec 8
  manualOrderIndicator : BitVec 8
  possRetransFlag : BitVec 8
  splitMsg : BitVec 8
  crossType : BitVec 8
  execInst : BitVec 8
  executionMode : ExecutionMode
  liquidityFlag : BitVec 8
  managedOrder : BitVec 8
  shortSaleType : BitVec 8
  delayToTime : BitVec 64
  deriving DecidableEq, Repr

namespace ExecutionReportModify

def encode (message : ExecutionReportModify) : List UInt8 :=
  encodeUIntLE 4 message.seqNum
    ++ encodeUIntLE 8 message.uuid
    ++ Alpha.encode message.execId
    ++ Alpha.encode message.senderId
    ++ Alpha.encode message.clordid
    ++ encodeUIntLE 8 message.partyDetailsListReqId
    ++ encodeUIntLE 8 message.orderId
    ++ encodeUIntLE 8 message.price
    ++ encodeUIntLE 8 message.stopPx
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.sendingTimeEpoch
    ++ encodeUIntLE 8 message.orderRequestId
    ++ encodeUIntLE 8 message.crossIdOptional
    ++ encodeUIntLE 8 message.hostCrossId
    ++ Alpha.encode message.location
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 4 message.orderQty
    ++ encodeUIntLE 4 message.cumQty
    ++ encodeUIntLE 4 message.leavesQty
    ++ encodeUIntLE 4 message.minQty
    ++ encodeUIntLE 4 message.displayQty
    ++ encodeUIntLE 2 message.expireDate
    ++ encodeUIntLE 2 message.delayDuration
    ++ OrdTypeOptional.encode message.ordTypeOptional
    ++ encodeUInt 1 message.side
    ++ encodeUInt 1 message.timeInForce
    ++ encodeUInt 1 message.manualOrderIndicator
    ++ encodeUInt 1 message.possRetransFlag
    ++ encodeUInt 1 message.splitMsg
    ++ encodeUInt 1 message.crossType
    ++ encodeUIntLE 1 message.execInst
    ++ ExecutionMode.encode message.executionMode
    ++ encodeUInt 1 message.liquidityFlag
    ++ encodeUInt 1 message.managedOrder
    ++ encodeUInt 1 message.shortSaleType
    ++ encodeUIntLE 8 message.delayToTime

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ExecutionReportModify × List UInt8) := do
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (uuid, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← Alpha.decode 40 bytes
  let (senderId, bytes) ← Alpha.decode 20 bytes
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (partyDetailsListReqId, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (stopPx, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (sendingTimeEpoch, bytes) ← decodeUIntLE 8 bytes
  let (orderRequestId, bytes) ← decodeUIntLE 8 bytes
  let (crossIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (hostCrossId, bytes) ← decodeUIntLE 8 bytes
  let (location, bytes) ← Alpha.decode 5 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (cumQty, bytes) ← decodeUIntLE 4 bytes
  let (leavesQty, bytes) ← decodeUIntLE 4 bytes
  let (minQty, bytes) ← decodeUIntLE 4 bytes
  let (displayQty, bytes) ← decodeUIntLE 4 bytes
  let (expireDate, bytes) ← decodeUIntLE 2 bytes
  let (delayDuration, bytes) ← decodeUIntLE 2 bytes
  let (ordTypeOptional, bytes) ← OrdTypeOptional.decode bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (manualOrderIndicator, bytes) ← decodeUInt 1 bytes
  let (possRetransFlag, bytes) ← decodeUInt 1 bytes
  let (splitMsg, bytes) ← decodeUInt 1 bytes
  let (crossType, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUIntLE 1 bytes
  let (executionMode, bytes) ← ExecutionMode.decode bytes
  let (liquidityFlag, bytes) ← decodeUInt 1 bytes
  let (managedOrder, bytes) ← decodeUInt 1 bytes
  let (shortSaleType, bytes) ← decodeUInt 1 bytes
  let (delayToTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ seqNum, uuid, execId, senderId, clordid, partyDetailsListReqId, orderId, price, stopPx, transactTime, sendingTimeEpoch, orderRequestId, crossIdOptional, hostCrossId, location, securityId, orderQty, cumQty, leavesQty, minQty, displayQty, expireDate, delayDuration, ordTypeOptional, side, timeInForce, manualOrderIndicator, possRetransFlag, splitMsg, crossType, execInst, executionMode, liquidityFlag, managedOrder, shortSaleType, delayToTime }, bytes)

@[simp] theorem encode_length (message : ExecutionReportModify) : (encode message).length = 217 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, OrdTypeOptional.encode_length, encodeUInt_length, ExecutionMode.encode_length]

theorem encode_length_pos (message : ExecutionReportModify) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutionReportModify) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [OrdTypeOptional.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [ExecutionMode.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end ExecutionReportModify

/-- Execution Report Status: 480 bytes -/
structure ExecutionReportStatus where
  seqNum : BitVec 32
  uuid : BitVec 64
  text : Alpha 256
  execId : Alpha 40
  senderId : Alpha 20
  clordid : Alpha 20
  partyDetailsListReqId : BitVec 64
  orderId : BitVec 64
  priceOptional : BitVec 64
  stopPx : BitVec 64
  transactTime : BitVec 64
  sendingTimeEpoch : BitVec 64
  orderRequestId : BitVec 64
  ordStatusReqIdOptional : BitVec 64
  massStatusReqIdOptional : BitVec 64
  crossIdOptional : BitVec 64
  hostCrossId : BitVec 64
  location : Alpha 5
  securityId : BitVec 32
  orderQty : BitVec 32
  cumQty : BitVec 32
  leavesQty : BitVec 32
  minQty : BitVec 32
  displayQty : BitVec 32
  expireDate : BitVec 16
  ordStatus : OrdStatus
  ordTypeOptional : OrdTypeOptional
  side : BitVec 8
  timeInForce : BitVec 8
  manualOrderIndicator : BitVec 8
  possRetransFlag : BitVec 8
  lastRptRequested : BitVec 8
  crossType : BitVec 8
  execInst : BitVec 8
  executionMode : ExecutionMode
  liquidityFlag : BitVec 8
  managedOrder : BitVec 8
  shortSaleType : BitVec 8
  deriving DecidableEq, Repr

namespace ExecutionReportStatus

def encode (message : ExecutionReportStatus) : List UInt8 :=
  encodeUIntLE 4 message.seqNum
    ++ encodeUIntLE 8 message.uuid
    ++ Alpha.encode message.text
    ++ Alpha.encode message.execId
    ++ Alpha.encode message.senderId
    ++ Alpha.encode message.clordid
    ++ encodeUIntLE 8 message.partyDetailsListReqId
    ++ encodeUIntLE 8 message.orderId
    ++ encodeUIntLE 8 message.priceOptional
    ++ encodeUIntLE 8 message.stopPx
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.sendingTimeEpoch
    ++ encodeUIntLE 8 message.orderRequestId
    ++ encodeUIntLE 8 message.ordStatusReqIdOptional
    ++ encodeUIntLE 8 message.massStatusReqIdOptional
    ++ encodeUIntLE 8 message.crossIdOptional
    ++ encodeUIntLE 8 message.hostCrossId
    ++ Alpha.encode message.location
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 4 message.orderQty
    ++ encodeUIntLE 4 message.cumQty
    ++ encodeUIntLE 4 message.leavesQty
    ++ encodeUIntLE 4 message.minQty
    ++ encodeUIntLE 4 message.displayQty
    ++ encodeUIntLE 2 message.expireDate
    ++ OrdStatus.encode message.ordStatus
    ++ OrdTypeOptional.encode message.ordTypeOptional
    ++ encodeUInt 1 message.side
    ++ encodeUInt 1 message.timeInForce
    ++ encodeUInt 1 message.manualOrderIndicator
    ++ encodeUInt 1 message.possRetransFlag
    ++ encodeUInt 1 message.lastRptRequested
    ++ encodeUInt 1 message.crossType
    ++ encodeUIntLE 1 message.execInst
    ++ ExecutionMode.encode message.executionMode
    ++ encodeUInt 1 message.liquidityFlag
    ++ encodeUInt 1 message.managedOrder
    ++ encodeUInt 1 message.shortSaleType

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ExecutionReportStatus × List UInt8) := do
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (uuid, bytes) ← decodeUIntLE 8 bytes
  let (text, bytes) ← Alpha.decode 256 bytes
  let (execId, bytes) ← Alpha.decode 40 bytes
  let (senderId, bytes) ← Alpha.decode 20 bytes
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (partyDetailsListReqId, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (priceOptional, bytes) ← decodeUIntLE 8 bytes
  let (stopPx, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (sendingTimeEpoch, bytes) ← decodeUIntLE 8 bytes
  let (orderRequestId, bytes) ← decodeUIntLE 8 bytes
  let (ordStatusReqIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (massStatusReqIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (crossIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (hostCrossId, bytes) ← decodeUIntLE 8 bytes
  let (location, bytes) ← Alpha.decode 5 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (cumQty, bytes) ← decodeUIntLE 4 bytes
  let (leavesQty, bytes) ← decodeUIntLE 4 bytes
  let (minQty, bytes) ← decodeUIntLE 4 bytes
  let (displayQty, bytes) ← decodeUIntLE 4 bytes
  let (expireDate, bytes) ← decodeUIntLE 2 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (ordTypeOptional, bytes) ← OrdTypeOptional.decode bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (manualOrderIndicator, bytes) ← decodeUInt 1 bytes
  let (possRetransFlag, bytes) ← decodeUInt 1 bytes
  let (lastRptRequested, bytes) ← decodeUInt 1 bytes
  let (crossType, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUIntLE 1 bytes
  let (executionMode, bytes) ← ExecutionMode.decode bytes
  let (liquidityFlag, bytes) ← decodeUInt 1 bytes
  let (managedOrder, bytes) ← decodeUInt 1 bytes
  let (shortSaleType, bytes) ← decodeUInt 1 bytes
  pure ({ seqNum, uuid, text, execId, senderId, clordid, partyDetailsListReqId, orderId, priceOptional, stopPx, transactTime, sendingTimeEpoch, orderRequestId, ordStatusReqIdOptional, massStatusReqIdOptional, crossIdOptional, hostCrossId, location, securityId, orderQty, cumQty, leavesQty, minQty, displayQty, expireDate, ordStatus, ordTypeOptional, side, timeInForce, manualOrderIndicator, possRetransFlag, lastRptRequested, crossType, execInst, executionMode, liquidityFlag, managedOrder, shortSaleType }, bytes)

@[simp] theorem encode_length (message : ExecutionReportStatus) : (encode message).length = 480 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, OrdStatus.encode_length, OrdTypeOptional.encode_length, encodeUInt_length, ExecutionMode.encode_length]

theorem encode_length_pos (message : ExecutionReportStatus) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutionReportStatus) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [OrdStatus.decode_encode]
  simp only [Option.bind_some]
  rw [OrdTypeOptional.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [ExecutionMode.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end ExecutionReportStatus

/-- Execution Report Cancel: 214 bytes -/
structure ExecutionReportCancel where
  seqNum : BitVec 32
  uuid : BitVec 64
  execId : Alpha 40
  senderId : Alpha 20
  clordid : Alpha 20
  partyDetailsListReqId : BitVec 64
  orderId : BitVec 64
  price : BitVec 64
  stopPx : BitVec 64
  transactTime : BitVec 64
  sendingTimeEpoch : BitVec 64
  orderRequestId : BitVec 64
  crossIdOptional : BitVec 64
  hostCrossId : BitVec 64
  location : Alpha 5
  securityId : BitVec 32
  orderQty : BitVec 32
  cumQty : BitVec 32
  minQty : BitVec 32
  displayQty : BitVec 32
  expireDate : BitVec 16
  delayDuration : BitVec 16
  ordTypeOptional : OrdTypeOptional
  side : BitVec 8
  timeInForce : BitVec 8
  manualOrderIndicator : BitVec 8
  possRetransFlag : BitVec 8
  splitMsg : BitVec 8
  execRestatementReason : BitVec 8
  crossType : BitVec 8
  execInst : BitVec 8
  executionMode : ExecutionMode
  liquidityFlag : BitVec 8
  managedOrder : BitVec 8
  shortSaleType : BitVec 8
  delayToTime : BitVec 64
  deriving DecidableEq, Repr

namespace ExecutionReportCancel

def encode (message : ExecutionReportCancel) : List UInt8 :=
  encodeUIntLE 4 message.seqNum
    ++ encodeUIntLE 8 message.uuid
    ++ Alpha.encode message.execId
    ++ Alpha.encode message.senderId
    ++ Alpha.encode message.clordid
    ++ encodeUIntLE 8 message.partyDetailsListReqId
    ++ encodeUIntLE 8 message.orderId
    ++ encodeUIntLE 8 message.price
    ++ encodeUIntLE 8 message.stopPx
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.sendingTimeEpoch
    ++ encodeUIntLE 8 message.orderRequestId
    ++ encodeUIntLE 8 message.crossIdOptional
    ++ encodeUIntLE 8 message.hostCrossId
    ++ Alpha.encode message.location
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 4 message.orderQty
    ++ encodeUIntLE 4 message.cumQty
    ++ encodeUIntLE 4 message.minQty
    ++ encodeUIntLE 4 message.displayQty
    ++ encodeUIntLE 2 message.expireDate
    ++ encodeUIntLE 2 message.delayDuration
    ++ OrdTypeOptional.encode message.ordTypeOptional
    ++ encodeUInt 1 message.side
    ++ encodeUInt 1 message.timeInForce
    ++ encodeUInt 1 message.manualOrderIndicator
    ++ encodeUInt 1 message.possRetransFlag
    ++ encodeUInt 1 message.splitMsg
    ++ encodeUInt 1 message.execRestatementReason
    ++ encodeUInt 1 message.crossType
    ++ encodeUIntLE 1 message.execInst
    ++ ExecutionMode.encode message.executionMode
    ++ encodeUInt 1 message.liquidityFlag
    ++ encodeUInt 1 message.managedOrder
    ++ encodeUInt 1 message.shortSaleType
    ++ encodeUIntLE 8 message.delayToTime

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ExecutionReportCancel × List UInt8) := do
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (uuid, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← Alpha.decode 40 bytes
  let (senderId, bytes) ← Alpha.decode 20 bytes
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (partyDetailsListReqId, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (stopPx, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (sendingTimeEpoch, bytes) ← decodeUIntLE 8 bytes
  let (orderRequestId, bytes) ← decodeUIntLE 8 bytes
  let (crossIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (hostCrossId, bytes) ← decodeUIntLE 8 bytes
  let (location, bytes) ← Alpha.decode 5 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (cumQty, bytes) ← decodeUIntLE 4 bytes
  let (minQty, bytes) ← decodeUIntLE 4 bytes
  let (displayQty, bytes) ← decodeUIntLE 4 bytes
  let (expireDate, bytes) ← decodeUIntLE 2 bytes
  let (delayDuration, bytes) ← decodeUIntLE 2 bytes
  let (ordTypeOptional, bytes) ← OrdTypeOptional.decode bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (manualOrderIndicator, bytes) ← decodeUInt 1 bytes
  let (possRetransFlag, bytes) ← decodeUInt 1 bytes
  let (splitMsg, bytes) ← decodeUInt 1 bytes
  let (execRestatementReason, bytes) ← decodeUInt 1 bytes
  let (crossType, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUIntLE 1 bytes
  let (executionMode, bytes) ← ExecutionMode.decode bytes
  let (liquidityFlag, bytes) ← decodeUInt 1 bytes
  let (managedOrder, bytes) ← decodeUInt 1 bytes
  let (shortSaleType, bytes) ← decodeUInt 1 bytes
  let (delayToTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ seqNum, uuid, execId, senderId, clordid, partyDetailsListReqId, orderId, price, stopPx, transactTime, sendingTimeEpoch, orderRequestId, crossIdOptional, hostCrossId, location, securityId, orderQty, cumQty, minQty, displayQty, expireDate, delayDuration, ordTypeOptional, side, timeInForce, manualOrderIndicator, possRetransFlag, splitMsg, execRestatementReason, crossType, execInst, executionMode, liquidityFlag, managedOrder, shortSaleType, delayToTime }, bytes)

@[simp] theorem encode_length (message : ExecutionReportCancel) : (encode message).length = 214 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, OrdTypeOptional.encode_length, encodeUInt_length, ExecutionMode.encode_length]

theorem encode_length_pos (message : ExecutionReportCancel) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutionReportCancel) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [OrdTypeOptional.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [ExecutionMode.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end ExecutionReportCancel

/-- Order Cancel Reject: 409 bytes -/
structure OrderCancelReject where
  seqNum : BitVec 32
  uuid : BitVec 64
  text : Alpha 256
  execId : Alpha 40
  senderId : Alpha 20
  clordid : Alpha 20
  partyDetailsListReqId : BitVec 64
  orderId : BitVec 64
  transactTime : BitVec 64
  sendingTimeEpoch : BitVec 64
  orderRequestId : BitVec 64
  location : Alpha 5
  cxlRejReason : BitVec 16
  delayDuration : BitVec 16
  manualOrderIndicator : BitVec 8
  possRetransFlag : BitVec 8
  splitMsg : BitVec 8
  liquidityFlag : BitVec 8
  delayToTime : BitVec 64
  deriving DecidableEq, Repr

namespace OrderCancelReject

def encode (message : OrderCancelReject) : List UInt8 :=
  encodeUIntLE 4 message.seqNum
    ++ encodeUIntLE 8 message.uuid
    ++ Alpha.encode message.text
    ++ Alpha.encode message.execId
    ++ Alpha.encode message.senderId
    ++ Alpha.encode message.clordid
    ++ encodeUIntLE 8 message.partyDetailsListReqId
    ++ encodeUIntLE 8 message.orderId
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.sendingTimeEpoch
    ++ encodeUIntLE 8 message.orderRequestId
    ++ Alpha.encode message.location
    ++ encodeUIntLE 2 message.cxlRejReason
    ++ encodeUIntLE 2 message.delayDuration
    ++ encodeUInt 1 message.manualOrderIndicator
    ++ encodeUInt 1 message.possRetransFlag
    ++ encodeUInt 1 message.splitMsg
    ++ encodeUInt 1 message.liquidityFlag
    ++ encodeUIntLE 8 message.delayToTime

def decode (bytes : List UInt8) : Option (OrderCancelReject × List UInt8) := do
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (uuid, bytes) ← decodeUIntLE 8 bytes
  let (text, bytes) ← Alpha.decode 256 bytes
  let (execId, bytes) ← Alpha.decode 40 bytes
  let (senderId, bytes) ← Alpha.decode 20 bytes
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (partyDetailsListReqId, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (sendingTimeEpoch, bytes) ← decodeUIntLE 8 bytes
  let (orderRequestId, bytes) ← decodeUIntLE 8 bytes
  let (location, bytes) ← Alpha.decode 5 bytes
  let (cxlRejReason, bytes) ← decodeUIntLE 2 bytes
  let (delayDuration, bytes) ← decodeUIntLE 2 bytes
  let (manualOrderIndicator, bytes) ← decodeUInt 1 bytes
  let (possRetransFlag, bytes) ← decodeUInt 1 bytes
  let (splitMsg, bytes) ← decodeUInt 1 bytes
  let (liquidityFlag, bytes) ← decodeUInt 1 bytes
  let (delayToTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ seqNum, uuid, text, execId, senderId, clordid, partyDetailsListReqId, orderId, transactTime, sendingTimeEpoch, orderRequestId, location, cxlRejReason, delayDuration, manualOrderIndicator, possRetransFlag, splitMsg, liquidityFlag, delayToTime }, bytes)

@[simp] theorem encode_length (message : OrderCancelReject) : (encode message).length = 409 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : OrderCancelReject) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancelReject) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end OrderCancelReject

/-- Order Cancel Replace Reject: 409 bytes -/
structure OrderCancelReplaceReject where
  seqNum : BitVec 32
  uuid : BitVec 64
  text : Alpha 256
  execId : Alpha 40
  senderId : Alpha 20
  clordid : Alpha 20
  partyDetailsListReqId : BitVec 64
  orderId : BitVec 64
  transactTime : BitVec 64
  sendingTimeEpoch : BitVec 64
  orderRequestId : BitVec 64
  location : Alpha 5
  cxlRejReason : BitVec 16
  delayDuration : BitVec 16
  manualOrderIndicator : BitVec 8
  possRetransFlag : BitVec 8
  splitMsg : BitVec 8
  liquidityFlag : BitVec 8
  delayToTime : BitVec 64
  deriving DecidableEq, Repr

namespace OrderCancelReplaceReject

def encode (message : OrderCancelReplaceReject) : List UInt8 :=
  encodeUIntLE 4 message.seqNum
    ++ encodeUIntLE 8 message.uuid
    ++ Alpha.encode message.text
    ++ Alpha.encode message.execId
    ++ Alpha.encode message.senderId
    ++ Alpha.encode message.clordid
    ++ encodeUIntLE 8 message.partyDetailsListReqId
    ++ encodeUIntLE 8 message.orderId
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.sendingTimeEpoch
    ++ encodeUIntLE 8 message.orderRequestId
    ++ Alpha.encode message.location
    ++ encodeUIntLE 2 message.cxlRejReason
    ++ encodeUIntLE 2 message.delayDuration
    ++ encodeUInt 1 message.manualOrderIndicator
    ++ encodeUInt 1 message.possRetransFlag
    ++ encodeUInt 1 message.splitMsg
    ++ encodeUInt 1 message.liquidityFlag
    ++ encodeUIntLE 8 message.delayToTime

def decode (bytes : List UInt8) : Option (OrderCancelReplaceReject × List UInt8) := do
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (uuid, bytes) ← decodeUIntLE 8 bytes
  let (text, bytes) ← Alpha.decode 256 bytes
  let (execId, bytes) ← Alpha.decode 40 bytes
  let (senderId, bytes) ← Alpha.decode 20 bytes
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (partyDetailsListReqId, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (sendingTimeEpoch, bytes) ← decodeUIntLE 8 bytes
  let (orderRequestId, bytes) ← decodeUIntLE 8 bytes
  let (location, bytes) ← Alpha.decode 5 bytes
  let (cxlRejReason, bytes) ← decodeUIntLE 2 bytes
  let (delayDuration, bytes) ← decodeUIntLE 2 bytes
  let (manualOrderIndicator, bytes) ← decodeUInt 1 bytes
  let (possRetransFlag, bytes) ← decodeUInt 1 bytes
  let (splitMsg, bytes) ← decodeUInt 1 bytes
  let (liquidityFlag, bytes) ← decodeUInt 1 bytes
  let (delayToTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ seqNum, uuid, text, execId, senderId, clordid, partyDetailsListReqId, orderId, transactTime, sendingTimeEpoch, orderRequestId, location, cxlRejReason, delayDuration, manualOrderIndicator, possRetransFlag, splitMsg, liquidityFlag, delayToTime }, bytes)

@[simp] theorem encode_length (message : OrderCancelReplaceReject) : (encode message).length = 409 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : OrderCancelReplaceReject) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancelReplaceReject) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end OrderCancelReplaceReject

/-- Party Details List Report -/
structure PartyDetailsListReport where
  seqNum : BitVec 32
  uuid : BitVec 64
  avgPxGroupId : Alpha 20
  partyDetailsListReqId : BitVec 64
  partyDetailsListReportId : BitVec 64
  sendingTimeEpoch : BitVec 64
  selfMatchPreventionId : BitVec 64
  totNumParties : BitVec 16
  requestResult : BitVec 8
  lastFragment : BitVec 8
  custOrderCapacity : BitVec 8
  clearingAccountType : BitVec 8
  selfMatchPreventionInstruction : SelfMatchPreventionInstruction
  avgPxIndicator : BitVec 8
  clearingTradePriceType : BitVec 8
  cmtaGiveupCd : CmtaGiveupCd
  custOrderHandlingInst : CustOrderHandlingInst
  executor : BitVec 64
  idmShortCode : BitVec 64
  possRetransFlag : BitVec 8
  splitMsg : BitVec 8
  partyDetailsGroups : PartyDetailsGroups
  trdRegPublicationsGroups : TrdRegPublicationsGroups
  deriving DecidableEq, Repr

namespace PartyDetailsListReport

def encode (message : PartyDetailsListReport) : List UInt8 :=
  encodeUIntLE 4 message.seqNum
    ++ encodeUIntLE 8 message.uuid
    ++ Alpha.encode message.avgPxGroupId
    ++ encodeUIntLE 8 message.partyDetailsListReqId
    ++ encodeUIntLE 8 message.partyDetailsListReportId
    ++ encodeUIntLE 8 message.sendingTimeEpoch
    ++ encodeUIntLE 8 message.selfMatchPreventionId
    ++ encodeUIntLE 2 message.totNumParties
    ++ encodeUInt 1 message.requestResult
    ++ encodeUInt 1 message.lastFragment
    ++ encodeUInt 1 message.custOrderCapacity
    ++ encodeUInt 1 message.clearingAccountType
    ++ SelfMatchPreventionInstruction.encode message.selfMatchPreventionInstruction
    ++ encodeUInt 1 message.avgPxIndicator
    ++ encodeUInt 1 message.clearingTradePriceType
    ++ CmtaGiveupCd.encode message.cmtaGiveupCd
    ++ CustOrderHandlingInst.encode message.custOrderHandlingInst
    ++ encodeUIntLE 8 message.executor
    ++ encodeUIntLE 8 message.idmShortCode
    ++ encodeUInt 1 message.possRetransFlag
    ++ encodeUInt 1 message.splitMsg
    ++ PartyDetailsGroups.encode message.partyDetailsGroups
    ++ TrdRegPublicationsGroups.encode message.trdRegPublicationsGroups

def decode (bytes : List UInt8) : Option (PartyDetailsListReport × List UInt8) := do
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (uuid, bytes) ← decodeUIntLE 8 bytes
  let (avgPxGroupId, bytes) ← Alpha.decode 20 bytes
  let (partyDetailsListReqId, bytes) ← decodeUIntLE 8 bytes
  let (partyDetailsListReportId, bytes) ← decodeUIntLE 8 bytes
  let (sendingTimeEpoch, bytes) ← decodeUIntLE 8 bytes
  let (selfMatchPreventionId, bytes) ← decodeUIntLE 8 bytes
  let (totNumParties, bytes) ← decodeUIntLE 2 bytes
  let (requestResult, bytes) ← decodeUInt 1 bytes
  let (lastFragment, bytes) ← decodeUInt 1 bytes
  let (custOrderCapacity, bytes) ← decodeUInt 1 bytes
  let (clearingAccountType, bytes) ← decodeUInt 1 bytes
  let (selfMatchPreventionInstruction, bytes) ← SelfMatchPreventionInstruction.decode bytes
  let (avgPxIndicator, bytes) ← decodeUInt 1 bytes
  let (clearingTradePriceType, bytes) ← decodeUInt 1 bytes
  let (cmtaGiveupCd, bytes) ← CmtaGiveupCd.decode bytes
  let (custOrderHandlingInst, bytes) ← CustOrderHandlingInst.decode bytes
  let (executor, bytes) ← decodeUIntLE 8 bytes
  let (idmShortCode, bytes) ← decodeUIntLE 8 bytes
  let (possRetransFlag, bytes) ← decodeUInt 1 bytes
  let (splitMsg, bytes) ← decodeUInt 1 bytes
  let (partyDetailsGroups, bytes) ← PartyDetailsGroups.decode bytes
  let (trdRegPublicationsGroups, bytes) ← TrdRegPublicationsGroups.decode bytes
  pure ({ seqNum, uuid, avgPxGroupId, partyDetailsListReqId, partyDetailsListReportId, sendingTimeEpoch, selfMatchPreventionId, totNumParties, requestResult, lastFragment, custOrderCapacity, clearingAccountType, selfMatchPreventionInstruction, avgPxIndicator, clearingTradePriceType, cmtaGiveupCd, custOrderHandlingInst, executor, idmShortCode, possRetransFlag, splitMsg, partyDetailsGroups, trdRegPublicationsGroups }, bytes)

theorem encode_length_pos (message : PartyDetailsListReport) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : PartyDetailsListReport) : (encode message).length ≤ 6219 := by
  have bound_partyDetailsGroups := PartyDetailsGroups.encode_length_le message.partyDetailsGroups
  have bound_trdRegPublicationsGroups := TrdRegPublicationsGroups.encode_length_le message.trdRegPublicationsGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length, SelfMatchPreventionInstruction.encode_length, CmtaGiveupCd.encode_length, CustOrderHandlingInst.encode_length]
  omega

@[simp] theorem decode_encode (message : PartyDetailsListReport) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [SelfMatchPreventionInstruction.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [CmtaGiveupCd.decode_encode]
  simp only [Option.bind_some]
  rw [CustOrderHandlingInst.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [PartyDetailsGroups.decode_encode]
  simp only [Option.bind_some]
  rw [TrdRegPublicationsGroups.decode_encode, Option.bind_some]
  rfl

end PartyDetailsListReport

/-- Execution Ack: 101 bytes -/
structure ExecutionAck where
  partyDetailsListReqId : BitVec 64
  orderId : BitVec 64
  execAckStatus : BitVec 8
  seqNum : BitVec 32
  clordid : Alpha 20
  secExecId : BitVec 64
  lastPx : BitVec 64
  securityId : BitVec 32
  lastQty : BitVec 32
  dkReason : DkReason
  side : BitVec 8
  senderId : Alpha 20
  sendingTimeEpoch : BitVec 64
  location : Alpha 5
  manualOrderIndicator : BitVec 8
  deriving DecidableEq, Repr

namespace ExecutionAck

def encode (message : ExecutionAck) : List UInt8 :=
  encodeUIntLE 8 message.partyDetailsListReqId
    ++ encodeUIntLE 8 message.orderId
    ++ encodeUInt 1 message.execAckStatus
    ++ encodeUIntLE 4 message.seqNum
    ++ Alpha.encode message.clordid
    ++ encodeUIntLE 8 message.secExecId
    ++ encodeUIntLE 8 message.lastPx
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 4 message.lastQty
    ++ DkReason.encode message.dkReason
    ++ encodeUInt 1 message.side
    ++ Alpha.encode message.senderId
    ++ encodeUIntLE 8 message.sendingTimeEpoch
    ++ Alpha.encode message.location
    ++ encodeUInt 1 message.manualOrderIndicator

def decode (bytes : List UInt8) : Option (ExecutionAck × List UInt8) := do
  let (partyDetailsListReqId, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (execAckStatus, bytes) ← decodeUInt 1 bytes
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (secExecId, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (dkReason, bytes) ← DkReason.decode bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (senderId, bytes) ← Alpha.decode 20 bytes
  let (sendingTimeEpoch, bytes) ← decodeUIntLE 8 bytes
  let (location, bytes) ← Alpha.decode 5 bytes
  let (manualOrderIndicator, bytes) ← decodeUInt 1 bytes
  pure ({ partyDetailsListReqId, orderId, execAckStatus, seqNum, clordid, secExecId, lastPx, securityId, lastQty, dkReason, side, senderId, sendingTimeEpoch, location, manualOrderIndicator }, bytes)

@[simp] theorem encode_length (message : ExecutionAck) : (encode message).length = 101 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, DkReason.encode_length]

theorem encode_length_pos (message : ExecutionAck) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutionAck) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [DkReason.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end ExecutionAck

/-- Quote Ack Entries Group: 11 bytes -/
structure QuoteAckEntriesGroup where
  quoteEntryId : BitVec 32
  securityId : BitVec 32
  quoteSetId : BitVec 16
  quoteEntryRejectReason : BitVec 8
  deriving DecidableEq, Repr

namespace QuoteAckEntriesGroup

def encode (message : QuoteAckEntriesGroup) : List UInt8 :=
  encodeUIntLE 4 message.quoteEntryId
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 2 message.quoteSetId
    ++ encodeUInt 1 message.quoteEntryRejectReason

def decode (bytes : List UInt8) : Option (QuoteAckEntriesGroup × List UInt8) := do
  let (quoteEntryId, bytes) ← decodeUIntLE 4 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (quoteSetId, bytes) ← decodeUIntLE 2 bytes
  let (quoteEntryRejectReason, bytes) ← decodeUInt 1 bytes
  pure ({ quoteEntryId, securityId, quoteSetId, quoteEntryRejectReason }, bytes)

@[simp] theorem encode_length (message : QuoteAckEntriesGroup) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : QuoteAckEntriesGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteAckEntriesGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end QuoteAckEntriesGroup

/-- Quote Ack Entries Groups -/
structure QuoteAckEntriesGroups where
  blockLength : BitVec 16
  quoteAckEntriesGroup : Bounded 1 QuoteAckEntriesGroup
  deriving DecidableEq, Repr

namespace QuoteAckEntriesGroups

def encode (message : QuoteAckEntriesGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.quoteAckEntriesGroup.val.length)
    ++ encodeMany QuoteAckEntriesGroup.encode message.quoteAckEntriesGroup.val

def decode (bytes : List UInt8) : Option (QuoteAckEntriesGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (quoteAckEntriesGroup_, bytes) ← decodeMany QuoteAckEntriesGroup.decode numInGroup.toNat bytes
  if fits_quoteAckEntriesGroup : quoteAckEntriesGroup_.length < 256 ^ 1 then
    pure ({ blockLength, quoteAckEntriesGroup := ⟨quoteAckEntriesGroup_, fits_quoteAckEntriesGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : QuoteAckEntriesGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : QuoteAckEntriesGroups) : (encode message).length ≤ 2808 := by
  have bound_quoteAckEntriesGroup := message.quoteAckEntriesGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const QuoteAckEntriesGroup.encode 11 QuoteAckEntriesGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : QuoteAckEntriesGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 QuoteAckEntriesGroup.encode QuoteAckEntriesGroup.decode QuoteAckEntriesGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.quoteAckEntriesGroup.length_lt, ↓reduceDIte]
  rfl

end QuoteAckEntriesGroups

/-- Mass Quote Ack -/
structure MassQuoteAck where
  seqNum : BitVec 32
  uuid : BitVec 64
  text : Alpha 256
  senderId : Alpha 20
  partyDetailsListReqId : BitVec 64
  requestTime : BitVec 64
  sendingTimeEpoch : BitVec 64
  quoteReqIdOptional : BitVec 64
  location : Alpha 5
  quoteId : BitVec 32
  quoteRejectReason : BitVec 16
  delayDuration : BitVec 16
  quoteAckStatus : BitVec 8
  manualOrderIndicator : BitVec 8
  noProcessedQuotes : BitVec 8
  mmProtectionReset : BitVec 8
  splitMsg : BitVec 8
  liquidityFlag : BitVec 8
  shortSaleType : BitVec 8
  totNoQuoteEntriesOptional : BitVec 8
  possRetransFlag : BitVec 8
  delayToTime : BitVec 64
  quoteAckEntriesGroups : QuoteAckEntriesGroups
  deriving DecidableEq, Repr

namespace MassQuoteAck

def encode (message : MassQuoteAck) : List UInt8 :=
  encodeUIntLE 4 message.seqNum
    ++ encodeUIntLE 8 message.uuid
    ++ Alpha.encode message.text
    ++ Alpha.encode message.senderId
    ++ encodeUIntLE 8 message.partyDetailsListReqId
    ++ encodeUIntLE 8 message.requestTime
    ++ encodeUIntLE 8 message.sendingTimeEpoch
    ++ encodeUIntLE 8 message.quoteReqIdOptional
    ++ Alpha.encode message.location
    ++ encodeUIntLE 4 message.quoteId
    ++ encodeUIntLE 2 message.quoteRejectReason
    ++ encodeUIntLE 2 message.delayDuration
    ++ encodeUInt 1 message.quoteAckStatus
    ++ encodeUInt 1 message.manualOrderIndicator
    ++ encodeUInt 1 message.noProcessedQuotes
    ++ encodeUInt 1 message.mmProtectionReset
    ++ encodeUInt 1 message.splitMsg
    ++ encodeUInt 1 message.liquidityFlag
    ++ encodeUInt 1 message.shortSaleType
    ++ encodeUInt 1 message.totNoQuoteEntriesOptional
    ++ encodeUInt 1 message.possRetransFlag
    ++ encodeUIntLE 8 message.delayToTime
    ++ QuoteAckEntriesGroups.encode message.quoteAckEntriesGroups

def decode (bytes : List UInt8) : Option (MassQuoteAck × List UInt8) := do
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (uuid, bytes) ← decodeUIntLE 8 bytes
  let (text, bytes) ← Alpha.decode 256 bytes
  let (senderId, bytes) ← Alpha.decode 20 bytes
  let (partyDetailsListReqId, bytes) ← decodeUIntLE 8 bytes
  let (requestTime, bytes) ← decodeUIntLE 8 bytes
  let (sendingTimeEpoch, bytes) ← decodeUIntLE 8 bytes
  let (quoteReqIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (location, bytes) ← Alpha.decode 5 bytes
  let (quoteId, bytes) ← decodeUIntLE 4 bytes
  let (quoteRejectReason, bytes) ← decodeUIntLE 2 bytes
  let (delayDuration, bytes) ← decodeUIntLE 2 bytes
  let (quoteAckStatus, bytes) ← decodeUInt 1 bytes
  let (manualOrderIndicator, bytes) ← decodeUInt 1 bytes
  let (noProcessedQuotes, bytes) ← decodeUInt 1 bytes
  let (mmProtectionReset, bytes) ← decodeUInt 1 bytes
  let (splitMsg, bytes) ← decodeUInt 1 bytes
  let (liquidityFlag, bytes) ← decodeUInt 1 bytes
  let (shortSaleType, bytes) ← decodeUInt 1 bytes
  let (totNoQuoteEntriesOptional, bytes) ← decodeUInt 1 bytes
  let (possRetransFlag, bytes) ← decodeUInt 1 bytes
  let (delayToTime, bytes) ← decodeUIntLE 8 bytes
  let (quoteAckEntriesGroups, bytes) ← QuoteAckEntriesGroups.decode bytes
  pure ({ seqNum, uuid, text, senderId, partyDetailsListReqId, requestTime, sendingTimeEpoch, quoteReqIdOptional, location, quoteId, quoteRejectReason, delayDuration, quoteAckStatus, manualOrderIndicator, noProcessedQuotes, mmProtectionReset, splitMsg, liquidityFlag, shortSaleType, totNoQuoteEntriesOptional, possRetransFlag, delayToTime, quoteAckEntriesGroups }, bytes)

theorem encode_length_pos (message : MassQuoteAck) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MassQuoteAck) : (encode message).length ≤ 3158 := by
  have bound_quoteAckEntriesGroups := QuoteAckEntriesGroups.encode_length_le message.quoteAckEntriesGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : MassQuoteAck) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [QuoteAckEntriesGroups.decode_encode, Option.bind_some]
  rfl

end MassQuoteAck

/-- Request For Quote Ack: 358 bytes -/
structure RequestForQuoteAck where
  seqNum : BitVec 32
  uuid : BitVec 64
  text : Alpha 256
  senderId : Alpha 20
  exchangeQuoteReqId : Alpha 17
  partyDetailsListReqId : BitVec 64
  requestTime : BitVec 64
  sendingTimeEpoch : BitVec 64
  quoteReqId : BitVec 64
  location : Alpha 5
  quoteRejectReason : BitVec 16
  delayDuration : BitVec 16
  quoteAckStatus : BitVec 8
  manualOrderIndicator : BitVec 8
  splitMsg : BitVec 8
  possRetransFlag : BitVec 8
  delayToTime : BitVec 64
  deriving DecidableEq, Repr

namespace RequestForQuoteAck

def encode (message : RequestForQuoteAck) : List UInt8 :=
  encodeUIntLE 4 message.seqNum
    ++ encodeUIntLE 8 message.uuid
    ++ Alpha.encode message.text
    ++ Alpha.encode message.senderId
    ++ Alpha.encode message.exchangeQuoteReqId
    ++ encodeUIntLE 8 message.partyDetailsListReqId
    ++ encodeUIntLE 8 message.requestTime
    ++ encodeUIntLE 8 message.sendingTimeEpoch
    ++ encodeUIntLE 8 message.quoteReqId
    ++ Alpha.encode message.location
    ++ encodeUIntLE 2 message.quoteRejectReason
    ++ encodeUIntLE 2 message.delayDuration
    ++ encodeUInt 1 message.quoteAckStatus
    ++ encodeUInt 1 message.manualOrderIndicator
    ++ encodeUInt 1 message.splitMsg
    ++ encodeUInt 1 message.possRetransFlag
    ++ encodeUIntLE 8 message.delayToTime

def decode (bytes : List UInt8) : Option (RequestForQuoteAck × List UInt8) := do
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (uuid, bytes) ← decodeUIntLE 8 bytes
  let (text, bytes) ← Alpha.decode 256 bytes
  let (senderId, bytes) ← Alpha.decode 20 bytes
  let (exchangeQuoteReqId, bytes) ← Alpha.decode 17 bytes
  let (partyDetailsListReqId, bytes) ← decodeUIntLE 8 bytes
  let (requestTime, bytes) ← decodeUIntLE 8 bytes
  let (sendingTimeEpoch, bytes) ← decodeUIntLE 8 bytes
  let (quoteReqId, bytes) ← decodeUIntLE 8 bytes
  let (location, bytes) ← Alpha.decode 5 bytes
  let (quoteRejectReason, bytes) ← decodeUIntLE 2 bytes
  let (delayDuration, bytes) ← decodeUIntLE 2 bytes
  let (quoteAckStatus, bytes) ← decodeUInt 1 bytes
  let (manualOrderIndicator, bytes) ← decodeUInt 1 bytes
  let (splitMsg, bytes) ← decodeUInt 1 bytes
  let (possRetransFlag, bytes) ← decodeUInt 1 bytes
  let (delayToTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ seqNum, uuid, text, senderId, exchangeQuoteReqId, partyDetailsListReqId, requestTime, sendingTimeEpoch, quoteReqId, location, quoteRejectReason, delayDuration, quoteAckStatus, manualOrderIndicator, splitMsg, possRetransFlag, delayToTime }, bytes)

@[simp] theorem encode_length (message : RequestForQuoteAck) : (encode message).length = 358 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : RequestForQuoteAck) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RequestForQuoteAck) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end RequestForQuoteAck

/-- Outright Trade Events Group: 27 bytes -/
structure OutrightTradeEventsGroup where
  orderEventPx : BitVec 64
  orderEventText : Alpha 5
  orderEventExecId : BitVec 32
  orderEventQty : BitVec 32
  tradeAddendum : BitVec 8
  orderEventReason : BitVec 8
  originalOrderEventExecId : BitVec 32
  deriving DecidableEq, Repr

namespace OutrightTradeEventsGroup

def encode (message : OutrightTradeEventsGroup) : List UInt8 :=
  encodeUIntLE 8 message.orderEventPx
    ++ Alpha.encode message.orderEventText
    ++ encodeUIntLE 4 message.orderEventExecId
    ++ encodeUIntLE 4 message.orderEventQty
    ++ encodeUInt 1 message.tradeAddendum
    ++ encodeUInt 1 message.orderEventReason
    ++ encodeUIntLE 4 message.originalOrderEventExecId

def decode (bytes : List UInt8) : Option (OutrightTradeEventsGroup × List UInt8) := do
  let (orderEventPx, bytes) ← decodeUIntLE 8 bytes
  let (orderEventText, bytes) ← Alpha.decode 5 bytes
  let (orderEventExecId, bytes) ← decodeUIntLE 4 bytes
  let (orderEventQty, bytes) ← decodeUIntLE 4 bytes
  let (tradeAddendum, bytes) ← decodeUInt 1 bytes
  let (orderEventReason, bytes) ← decodeUInt 1 bytes
  let (originalOrderEventExecId, bytes) ← decodeUIntLE 4 bytes
  pure ({ orderEventPx, orderEventText, orderEventExecId, orderEventQty, tradeAddendum, orderEventReason, originalOrderEventExecId }, bytes)

@[simp] theorem encode_length (message : OutrightTradeEventsGroup) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : OutrightTradeEventsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OutrightTradeEventsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end OutrightTradeEventsGroup

/-- Outright Trade Events Groups -/
structure OutrightTradeEventsGroups where
  blockLength : BitVec 16
  outrightTradeEventsGroup : Bounded 1 OutrightTradeEventsGroup
  deriving DecidableEq, Repr

namespace OutrightTradeEventsGroups

def encode (message : OutrightTradeEventsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.outrightTradeEventsGroup.val.length)
    ++ encodeMany OutrightTradeEventsGroup.encode message.outrightTradeEventsGroup.val

def decode (bytes : List UInt8) : Option (OutrightTradeEventsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (outrightTradeEventsGroup_, bytes) ← decodeMany OutrightTradeEventsGroup.decode numInGroup.toNat bytes
  if fits_outrightTradeEventsGroup : outrightTradeEventsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, outrightTradeEventsGroup := ⟨outrightTradeEventsGroup_, fits_outrightTradeEventsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : OutrightTradeEventsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OutrightTradeEventsGroups) : (encode message).length ≤ 6888 := by
  have bound_outrightTradeEventsGroup := message.outrightTradeEventsGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const OutrightTradeEventsGroup.encode 27 OutrightTradeEventsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : OutrightTradeEventsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 OutrightTradeEventsGroup.encode OutrightTradeEventsGroup.decode OutrightTradeEventsGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.outrightTradeEventsGroup.length_lt, ↓reduceDIte]
  rfl

end OutrightTradeEventsGroups

/-- Execution Report Trade Addendum Outright -/
structure ExecutionReportTradeAddendumOutright where
  seqNum : BitVec 32
  uuid : BitVec 64
  execId : Alpha 40
  senderId : Alpha 20
  clordid : Alpha 20
  partyDetailsListReqId : BitVec 64
  lastPx : BitVec 64
  orderId : BitVec 64
  transactTime : BitVec 64
  sendingTimeEpoch : BitVec 64
  secExecId : BitVec 64
  origSecondaryExecutionId : BitVec 64
  location : Alpha 5
  securityId : BitVec 32
  lastQty : BitVec 32
  sideTradeId : BitVec 32
  origSideTradeId : BitVec 32
  tradeDate : BitVec 16
  ordStatusTrdCxl : OrdStatusTrdCxl
  execType : ExecType
  side : BitVec 8
  manualOrderIndicator : BitVec 8
  possRetransFlag : BitVec 8
  execInst : BitVec 8
  executionMode : ExecutionMode
  liquidityFlag : BitVec 8
  managedOrder : BitVec 8
  shortSaleType : BitVec 8
  fillsGroups : FillsGroups
  outrightTradeEventsGroups : OutrightTradeEventsGroups
  deriving DecidableEq, Repr

namespace ExecutionReportTradeAddendumOutright

def encode (message : ExecutionReportTradeAddendumOutright) : List UInt8 :=
  encodeUIntLE 4 message.seqNum
    ++ encodeUIntLE 8 message.uuid
    ++ Alpha.encode message.execId
    ++ Alpha.encode message.senderId
    ++ Alpha.encode message.clordid
    ++ encodeUIntLE 8 message.partyDetailsListReqId
    ++ encodeUIntLE 8 message.lastPx
    ++ encodeUIntLE 8 message.orderId
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.sendingTimeEpoch
    ++ encodeUIntLE 8 message.secExecId
    ++ encodeUIntLE 8 message.origSecondaryExecutionId
    ++ Alpha.encode message.location
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 4 message.lastQty
    ++ encodeUIntLE 4 message.sideTradeId
    ++ encodeUIntLE 4 message.origSideTradeId
    ++ encodeUIntLE 2 message.tradeDate
    ++ OrdStatusTrdCxl.encode message.ordStatusTrdCxl
    ++ ExecType.encode message.execType
    ++ encodeUInt 1 message.side
    ++ encodeUInt 1 message.manualOrderIndicator
    ++ encodeUInt 1 message.possRetransFlag
    ++ encodeUIntLE 1 message.execInst
    ++ ExecutionMode.encode message.executionMode
    ++ encodeUInt 1 message.liquidityFlag
    ++ encodeUInt 1 message.managedOrder
    ++ encodeUInt 1 message.shortSaleType
    ++ FillsGroups.encode message.fillsGroups
    ++ OutrightTradeEventsGroups.encode message.outrightTradeEventsGroups

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ExecutionReportTradeAddendumOutright × List UInt8) := do
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (uuid, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← Alpha.decode 40 bytes
  let (senderId, bytes) ← Alpha.decode 20 bytes
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (partyDetailsListReqId, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (sendingTimeEpoch, bytes) ← decodeUIntLE 8 bytes
  let (secExecId, bytes) ← decodeUIntLE 8 bytes
  let (origSecondaryExecutionId, bytes) ← decodeUIntLE 8 bytes
  let (location, bytes) ← Alpha.decode 5 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (sideTradeId, bytes) ← decodeUIntLE 4 bytes
  let (origSideTradeId, bytes) ← decodeUIntLE 4 bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (ordStatusTrdCxl, bytes) ← OrdStatusTrdCxl.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (manualOrderIndicator, bytes) ← decodeUInt 1 bytes
  let (possRetransFlag, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUIntLE 1 bytes
  let (executionMode, bytes) ← ExecutionMode.decode bytes
  let (liquidityFlag, bytes) ← decodeUInt 1 bytes
  let (managedOrder, bytes) ← decodeUInt 1 bytes
  let (shortSaleType, bytes) ← decodeUInt 1 bytes
  let (fillsGroups, bytes) ← FillsGroups.decode bytes
  let (outrightTradeEventsGroups, bytes) ← OutrightTradeEventsGroups.decode bytes
  pure ({ seqNum, uuid, execId, senderId, clordid, partyDetailsListReqId, lastPx, orderId, transactTime, sendingTimeEpoch, secExecId, origSecondaryExecutionId, location, securityId, lastQty, sideTradeId, origSideTradeId, tradeDate, ordStatusTrdCxl, execType, side, manualOrderIndicator, possRetransFlag, execInst, executionMode, liquidityFlag, managedOrder, shortSaleType, fillsGroups, outrightTradeEventsGroups }, bytes)

theorem encode_length_pos (message : ExecutionReportTradeAddendumOutright) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ExecutionReportTradeAddendumOutright) : (encode message).length ≤ 10897 := by
  have bound_fillsGroups := FillsGroups.encode_length_le message.fillsGroups
  have bound_outrightTradeEventsGroups := OutrightTradeEventsGroups.encode_length_le message.outrightTradeEventsGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, OrdStatusTrdCxl.encode_length, ExecType.encode_length, encodeUInt_length, ExecutionMode.encode_length]
  omega

@[simp] theorem decode_encode (message : ExecutionReportTradeAddendumOutright) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [OrdStatusTrdCxl.decode_encode]
  simp only [Option.bind_some]
  rw [ExecType.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [ExecutionMode.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [FillsGroups.decode_encode]
  simp only [Option.bind_some]
  rw [OutrightTradeEventsGroups.decode_encode, Option.bind_some]
  rfl

end ExecutionReportTradeAddendumOutright

/-- Trade Addendum Legs Group: 41 bytes -/
structure TradeAddendumLegsGroup where
  legExecId : BitVec 64
  legLastPx : BitVec 64
  legExecRefId : BitVec 64
  legTradeId : BitVec 32
  legTradeRefId : BitVec 32
  legSecurityId : BitVec 32
  legLastQty : BitVec 32
  legSide : BitVec 8
  deriving DecidableEq, Repr

namespace TradeAddendumLegsGroup

def encode (message : TradeAddendumLegsGroup) : List UInt8 :=
  encodeUIntLE 8 message.legExecId
    ++ encodeUIntLE 8 message.legLastPx
    ++ encodeUIntLE 8 message.legExecRefId
    ++ encodeUIntLE 4 message.legTradeId
    ++ encodeUIntLE 4 message.legTradeRefId
    ++ encodeUIntLE 4 message.legSecurityId
    ++ encodeUIntLE 4 message.legLastQty
    ++ encodeUInt 1 message.legSide

def decode (bytes : List UInt8) : Option (TradeAddendumLegsGroup × List UInt8) := do
  let (legExecId, bytes) ← decodeUIntLE 8 bytes
  let (legLastPx, bytes) ← decodeUIntLE 8 bytes
  let (legExecRefId, bytes) ← decodeUIntLE 8 bytes
  let (legTradeId, bytes) ← decodeUIntLE 4 bytes
  let (legTradeRefId, bytes) ← decodeUIntLE 4 bytes
  let (legSecurityId, bytes) ← decodeUIntLE 4 bytes
  let (legLastQty, bytes) ← decodeUIntLE 4 bytes
  let (legSide, bytes) ← decodeUInt 1 bytes
  pure ({ legExecId, legLastPx, legExecRefId, legTradeId, legTradeRefId, legSecurityId, legLastQty, legSide }, bytes)

@[simp] theorem encode_length (message : TradeAddendumLegsGroup) : (encode message).length = 41 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : TradeAddendumLegsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeAddendumLegsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end TradeAddendumLegsGroup

/-- Trade Addendum Legs Groups -/
structure TradeAddendumLegsGroups where
  blockLength : BitVec 16
  tradeAddendumLegsGroup : Bounded 1 TradeAddendumLegsGroup
  deriving DecidableEq, Repr

namespace TradeAddendumLegsGroups

def encode (message : TradeAddendumLegsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.tradeAddendumLegsGroup.val.length)
    ++ encodeMany TradeAddendumLegsGroup.encode message.tradeAddendumLegsGroup.val

def decode (bytes : List UInt8) : Option (TradeAddendumLegsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (tradeAddendumLegsGroup_, bytes) ← decodeMany TradeAddendumLegsGroup.decode numInGroup.toNat bytes
  if fits_tradeAddendumLegsGroup : tradeAddendumLegsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, tradeAddendumLegsGroup := ⟨tradeAddendumLegsGroup_, fits_tradeAddendumLegsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : TradeAddendumLegsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TradeAddendumLegsGroups) : (encode message).length ≤ 10458 := by
  have bound_tradeAddendumLegsGroup := message.tradeAddendumLegsGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const TradeAddendumLegsGroup.encode 41 TradeAddendumLegsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : TradeAddendumLegsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 TradeAddendumLegsGroup.encode TradeAddendumLegsGroup.decode TradeAddendumLegsGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.tradeAddendumLegsGroup.length_lt, ↓reduceDIte]
  rfl

end TradeAddendumLegsGroups

/-- Spread Trade Events Group: 27 bytes -/
structure SpreadTradeEventsGroup where
  orderEventPx : BitVec 64
  orderEventText : Alpha 5
  orderEventExecId : BitVec 32
  orderEventQty : BitVec 32
  tradeAddendum : BitVec 8
  orderEventReason : BitVec 8
  originalOrderEventExecId : BitVec 32
  deriving DecidableEq, Repr

namespace SpreadTradeEventsGroup

def encode (message : SpreadTradeEventsGroup) : List UInt8 :=
  encodeUIntLE 8 message.orderEventPx
    ++ Alpha.encode message.orderEventText
    ++ encodeUIntLE 4 message.orderEventExecId
    ++ encodeUIntLE 4 message.orderEventQty
    ++ encodeUInt 1 message.tradeAddendum
    ++ encodeUInt 1 message.orderEventReason
    ++ encodeUIntLE 4 message.originalOrderEventExecId

def decode (bytes : List UInt8) : Option (SpreadTradeEventsGroup × List UInt8) := do
  let (orderEventPx, bytes) ← decodeUIntLE 8 bytes
  let (orderEventText, bytes) ← Alpha.decode 5 bytes
  let (orderEventExecId, bytes) ← decodeUIntLE 4 bytes
  let (orderEventQty, bytes) ← decodeUIntLE 4 bytes
  let (tradeAddendum, bytes) ← decodeUInt 1 bytes
  let (orderEventReason, bytes) ← decodeUInt 1 bytes
  let (originalOrderEventExecId, bytes) ← decodeUIntLE 4 bytes
  pure ({ orderEventPx, orderEventText, orderEventExecId, orderEventQty, tradeAddendum, orderEventReason, originalOrderEventExecId }, bytes)

@[simp] theorem encode_length (message : SpreadTradeEventsGroup) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SpreadTradeEventsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SpreadTradeEventsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end SpreadTradeEventsGroup

/-- Spread Trade Events Groups -/
structure SpreadTradeEventsGroups where
  blockLength : BitVec 16
  spreadTradeEventsGroup : Bounded 1 SpreadTradeEventsGroup
  deriving DecidableEq, Repr

namespace SpreadTradeEventsGroups

def encode (message : SpreadTradeEventsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.spreadTradeEventsGroup.val.length)
    ++ encodeMany SpreadTradeEventsGroup.encode message.spreadTradeEventsGroup.val

def decode (bytes : List UInt8) : Option (SpreadTradeEventsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (spreadTradeEventsGroup_, bytes) ← decodeMany SpreadTradeEventsGroup.decode numInGroup.toNat bytes
  if fits_spreadTradeEventsGroup : spreadTradeEventsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, spreadTradeEventsGroup := ⟨spreadTradeEventsGroup_, fits_spreadTradeEventsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : SpreadTradeEventsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SpreadTradeEventsGroups) : (encode message).length ≤ 6888 := by
  have bound_spreadTradeEventsGroup := message.spreadTradeEventsGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const SpreadTradeEventsGroup.encode 27 SpreadTradeEventsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : SpreadTradeEventsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 SpreadTradeEventsGroup.encode SpreadTradeEventsGroup.decode SpreadTradeEventsGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.spreadTradeEventsGroup.length_lt, ↓reduceDIte]
  rfl

end SpreadTradeEventsGroups

/-- Execution Report Trade Addendum Spread -/
structure ExecutionReportTradeAddendumSpread where
  seqNum : BitVec 32
  uuid : BitVec 64
  execId : Alpha 40
  senderId : Alpha 20
  clordid : Alpha 20
  partyDetailsListReqId : BitVec 64
  lastPx : BitVec 64
  orderId : BitVec 64
  transactTime : BitVec 64
  sendingTimeEpoch : BitVec 64
  secExecId : BitVec 64
  origSecondaryExecutionId : BitVec 64
  location : Alpha 5
  securityId : BitVec 32
  mdTradeEntryId : BitVec 32
  lastQty : BitVec 32
  sideTradeId : BitVec 32
  origSideTradeId : BitVec 32
  tradeDate : BitVec 16
  ordStatusTrdCxl : OrdStatusTrdCxl
  execType : ExecType
  ordTypeOptional : OrdTypeOptional
  side : BitVec 8
  manualOrderIndicator : BitVec 8
  possRetransFlag : BitVec 8
  totalNumSecurities : BitVec 8
  execInst : BitVec 8
  executionMode : ExecutionMode
  liquidityFlag : BitVec 8
  managedOrder : BitVec 8
  shortSaleType : BitVec 8
  fillsGroups : FillsGroups
  tradeAddendumLegsGroups : TradeAddendumLegsGroups
  spreadTradeEventsGroups : SpreadTradeEventsGroups
  deriving DecidableEq, Repr

namespace ExecutionReportTradeAddendumSpread

def encode (message : ExecutionReportTradeAddendumSpread) : List UInt8 :=
  encodeUIntLE 4 message.seqNum
    ++ encodeUIntLE 8 message.uuid
    ++ Alpha.encode message.execId
    ++ Alpha.encode message.senderId
    ++ Alpha.encode message.clordid
    ++ encodeUIntLE 8 message.partyDetailsListReqId
    ++ encodeUIntLE 8 message.lastPx
    ++ encodeUIntLE 8 message.orderId
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.sendingTimeEpoch
    ++ encodeUIntLE 8 message.secExecId
    ++ encodeUIntLE 8 message.origSecondaryExecutionId
    ++ Alpha.encode message.location
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 4 message.mdTradeEntryId
    ++ encodeUIntLE 4 message.lastQty
    ++ encodeUIntLE 4 message.sideTradeId
    ++ encodeUIntLE 4 message.origSideTradeId
    ++ encodeUIntLE 2 message.tradeDate
    ++ OrdStatusTrdCxl.encode message.ordStatusTrdCxl
    ++ ExecType.encode message.execType
    ++ OrdTypeOptional.encode message.ordTypeOptional
    ++ encodeUInt 1 message.side
    ++ encodeUInt 1 message.manualOrderIndicator
    ++ encodeUInt 1 message.possRetransFlag
    ++ encodeUInt 1 message.totalNumSecurities
    ++ encodeUIntLE 1 message.execInst
    ++ ExecutionMode.encode message.executionMode
    ++ encodeUInt 1 message.liquidityFlag
    ++ encodeUInt 1 message.managedOrder
    ++ encodeUInt 1 message.shortSaleType
    ++ FillsGroups.encode message.fillsGroups
    ++ TradeAddendumLegsGroups.encode message.tradeAddendumLegsGroups
    ++ SpreadTradeEventsGroups.encode message.spreadTradeEventsGroups

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ExecutionReportTradeAddendumSpread × List UInt8) := do
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (uuid, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← Alpha.decode 40 bytes
  let (senderId, bytes) ← Alpha.decode 20 bytes
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (partyDetailsListReqId, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (sendingTimeEpoch, bytes) ← decodeUIntLE 8 bytes
  let (secExecId, bytes) ← decodeUIntLE 8 bytes
  let (origSecondaryExecutionId, bytes) ← decodeUIntLE 8 bytes
  let (location, bytes) ← Alpha.decode 5 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (mdTradeEntryId, bytes) ← decodeUIntLE 4 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (sideTradeId, bytes) ← decodeUIntLE 4 bytes
  let (origSideTradeId, bytes) ← decodeUIntLE 4 bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (ordStatusTrdCxl, bytes) ← OrdStatusTrdCxl.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (ordTypeOptional, bytes) ← OrdTypeOptional.decode bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (manualOrderIndicator, bytes) ← decodeUInt 1 bytes
  let (possRetransFlag, bytes) ← decodeUInt 1 bytes
  let (totalNumSecurities, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUIntLE 1 bytes
  let (executionMode, bytes) ← ExecutionMode.decode bytes
  let (liquidityFlag, bytes) ← decodeUInt 1 bytes
  let (managedOrder, bytes) ← decodeUInt 1 bytes
  let (shortSaleType, bytes) ← decodeUInt 1 bytes
  let (fillsGroups, bytes) ← FillsGroups.decode bytes
  let (tradeAddendumLegsGroups, bytes) ← TradeAddendumLegsGroups.decode bytes
  let (spreadTradeEventsGroups, bytes) ← SpreadTradeEventsGroups.decode bytes
  pure ({ seqNum, uuid, execId, senderId, clordid, partyDetailsListReqId, lastPx, orderId, transactTime, sendingTimeEpoch, secExecId, origSecondaryExecutionId, location, securityId, mdTradeEntryId, lastQty, sideTradeId, origSideTradeId, tradeDate, ordStatusTrdCxl, execType, ordTypeOptional, side, manualOrderIndicator, possRetransFlag, totalNumSecurities, execInst, executionMode, liquidityFlag, managedOrder, shortSaleType, fillsGroups, tradeAddendumLegsGroups, spreadTradeEventsGroups }, bytes)

theorem encode_length_pos (message : ExecutionReportTradeAddendumSpread) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ExecutionReportTradeAddendumSpread) : (encode message).length ≤ 21361 := by
  have bound_fillsGroups := FillsGroups.encode_length_le message.fillsGroups
  have bound_tradeAddendumLegsGroups := TradeAddendumLegsGroups.encode_length_le message.tradeAddendumLegsGroups
  have bound_spreadTradeEventsGroups := SpreadTradeEventsGroups.encode_length_le message.spreadTradeEventsGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, OrdStatusTrdCxl.encode_length, ExecType.encode_length, OrdTypeOptional.encode_length, encodeUInt_length, ExecutionMode.encode_length]
  omega

@[simp] theorem decode_encode (message : ExecutionReportTradeAddendumSpread) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [OrdStatusTrdCxl.decode_encode]
  simp only [Option.bind_some]
  rw [ExecType.decode_encode]
  simp only [Option.bind_some]
  rw [OrdTypeOptional.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [ExecutionMode.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [FillsGroups.decode_encode]
  simp only [Option.bind_some]
  rw [TradeAddendumLegsGroups.decode_encode]
  simp only [Option.bind_some]
  rw [SpreadTradeEventsGroups.decode_encode, Option.bind_some]
  rfl

end ExecutionReportTradeAddendumSpread

/-- Spread Leg Trade Events Group: 27 bytes -/
structure SpreadLegTradeEventsGroup where
  orderEventPx : BitVec 64
  orderEventText : Alpha 5
  orderEventExecId : BitVec 32
  orderEventQty : BitVec 32
  tradeAddendum : BitVec 8
  orderEventReason : BitVec 8
  originalOrderEventExecId : BitVec 32
  deriving DecidableEq, Repr

namespace SpreadLegTradeEventsGroup

def encode (message : SpreadLegTradeEventsGroup) : List UInt8 :=
  encodeUIntLE 8 message.orderEventPx
    ++ Alpha.encode message.orderEventText
    ++ encodeUIntLE 4 message.orderEventExecId
    ++ encodeUIntLE 4 message.orderEventQty
    ++ encodeUInt 1 message.tradeAddendum
    ++ encodeUInt 1 message.orderEventReason
    ++ encodeUIntLE 4 message.originalOrderEventExecId

def decode (bytes : List UInt8) : Option (SpreadLegTradeEventsGroup × List UInt8) := do
  let (orderEventPx, bytes) ← decodeUIntLE 8 bytes
  let (orderEventText, bytes) ← Alpha.decode 5 bytes
  let (orderEventExecId, bytes) ← decodeUIntLE 4 bytes
  let (orderEventQty, bytes) ← decodeUIntLE 4 bytes
  let (tradeAddendum, bytes) ← decodeUInt 1 bytes
  let (orderEventReason, bytes) ← decodeUInt 1 bytes
  let (originalOrderEventExecId, bytes) ← decodeUIntLE 4 bytes
  pure ({ orderEventPx, orderEventText, orderEventExecId, orderEventQty, tradeAddendum, orderEventReason, originalOrderEventExecId }, bytes)

@[simp] theorem encode_length (message : SpreadLegTradeEventsGroup) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SpreadLegTradeEventsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SpreadLegTradeEventsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end SpreadLegTradeEventsGroup

/-- Spread Leg Trade Events Groups -/
structure SpreadLegTradeEventsGroups where
  blockLength : BitVec 16
  spreadLegTradeEventsGroup : Bounded 1 SpreadLegTradeEventsGroup
  deriving DecidableEq, Repr

namespace SpreadLegTradeEventsGroups

def encode (message : SpreadLegTradeEventsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.spreadLegTradeEventsGroup.val.length)
    ++ encodeMany SpreadLegTradeEventsGroup.encode message.spreadLegTradeEventsGroup.val

def decode (bytes : List UInt8) : Option (SpreadLegTradeEventsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (spreadLegTradeEventsGroup_, bytes) ← decodeMany SpreadLegTradeEventsGroup.decode numInGroup.toNat bytes
  if fits_spreadLegTradeEventsGroup : spreadLegTradeEventsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, spreadLegTradeEventsGroup := ⟨spreadLegTradeEventsGroup_, fits_spreadLegTradeEventsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : SpreadLegTradeEventsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SpreadLegTradeEventsGroups) : (encode message).length ≤ 6888 := by
  have bound_spreadLegTradeEventsGroup := message.spreadLegTradeEventsGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const SpreadLegTradeEventsGroup.encode 27 SpreadLegTradeEventsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : SpreadLegTradeEventsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 SpreadLegTradeEventsGroup.encode SpreadLegTradeEventsGroup.decode SpreadLegTradeEventsGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.spreadLegTradeEventsGroup.length_lt, ↓reduceDIte]
  rfl

end SpreadLegTradeEventsGroups

/-- Execution Report Trade Addendum Spread Leg -/
structure ExecutionReportTradeAddendumSpreadLeg where
  seqNum : BitVec 32
  uuid : BitVec 64
  execId : Alpha 40
  senderId : Alpha 20
  clordid : Alpha 20
  partyDetailsListReqId : BitVec 64
  lastPx : BitVec 64
  orderId : BitVec 64
  transactTime : BitVec 64
  sendingTimeEpoch : BitVec 64
  secExecId : BitVec 64
  origSecondaryExecutionId : BitVec 64
  location : Alpha 5
  securityId : BitVec 32
  lastQty : BitVec 32
  sideTradeId : BitVec 32
  origSideTradeId : BitVec 32
  tradeDate : BitVec 16
  ordStatusTrdCxl : OrdStatusTrdCxl
  execType : ExecType
  manualOrderIndicator : BitVec 8
  possRetransFlag : BitVec 8
  side : BitVec 8
  fillsGroups : FillsGroups
  spreadLegTradeEventsGroups : SpreadLegTradeEventsGroups
  deriving DecidableEq, Repr

namespace ExecutionReportTradeAddendumSpreadLeg

def encode (message : ExecutionReportTradeAddendumSpreadLeg) : List UInt8 :=
  encodeUIntLE 4 message.seqNum
    ++ encodeUIntLE 8 message.uuid
    ++ Alpha.encode message.execId
    ++ Alpha.encode message.senderId
    ++ Alpha.encode message.clordid
    ++ encodeUIntLE 8 message.partyDetailsListReqId
    ++ encodeUIntLE 8 message.lastPx
    ++ encodeUIntLE 8 message.orderId
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.sendingTimeEpoch
    ++ encodeUIntLE 8 message.secExecId
    ++ encodeUIntLE 8 message.origSecondaryExecutionId
    ++ Alpha.encode message.location
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 4 message.lastQty
    ++ encodeUIntLE 4 message.sideTradeId
    ++ encodeUIntLE 4 message.origSideTradeId
    ++ encodeUIntLE 2 message.tradeDate
    ++ OrdStatusTrdCxl.encode message.ordStatusTrdCxl
    ++ ExecType.encode message.execType
    ++ encodeUInt 1 message.manualOrderIndicator
    ++ encodeUInt 1 message.possRetransFlag
    ++ encodeUInt 1 message.side
    ++ FillsGroups.encode message.fillsGroups
    ++ SpreadLegTradeEventsGroups.encode message.spreadLegTradeEventsGroups

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ExecutionReportTradeAddendumSpreadLeg × List UInt8) := do
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (uuid, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← Alpha.decode 40 bytes
  let (senderId, bytes) ← Alpha.decode 20 bytes
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (partyDetailsListReqId, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (sendingTimeEpoch, bytes) ← decodeUIntLE 8 bytes
  let (secExecId, bytes) ← decodeUIntLE 8 bytes
  let (origSecondaryExecutionId, bytes) ← decodeUIntLE 8 bytes
  let (location, bytes) ← Alpha.decode 5 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (sideTradeId, bytes) ← decodeUIntLE 4 bytes
  let (origSideTradeId, bytes) ← decodeUIntLE 4 bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (ordStatusTrdCxl, bytes) ← OrdStatusTrdCxl.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (manualOrderIndicator, bytes) ← decodeUInt 1 bytes
  let (possRetransFlag, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (fillsGroups, bytes) ← FillsGroups.decode bytes
  let (spreadLegTradeEventsGroups, bytes) ← SpreadLegTradeEventsGroups.decode bytes
  pure ({ seqNum, uuid, execId, senderId, clordid, partyDetailsListReqId, lastPx, orderId, transactTime, sendingTimeEpoch, secExecId, origSecondaryExecutionId, location, securityId, lastQty, sideTradeId, origSideTradeId, tradeDate, ordStatusTrdCxl, execType, manualOrderIndicator, possRetransFlag, side, fillsGroups, spreadLegTradeEventsGroups }, bytes)

theorem encode_length_pos (message : ExecutionReportTradeAddendumSpreadLeg) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ExecutionReportTradeAddendumSpreadLeg) : (encode message).length ≤ 10892 := by
  have bound_fillsGroups := FillsGroups.encode_length_le message.fillsGroups
  have bound_spreadLegTradeEventsGroups := SpreadLegTradeEventsGroups.encode_length_le message.spreadLegTradeEventsGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, OrdStatusTrdCxl.encode_length, ExecType.encode_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : ExecutionReportTradeAddendumSpreadLeg) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [OrdStatusTrdCxl.decode_encode]
  simp only [Option.bind_some]
  rw [ExecType.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [FillsGroups.decode_encode]
  simp only [Option.bind_some]
  rw [SpreadLegTradeEventsGroups.decode_encode, Option.bind_some]
  rfl

end ExecutionReportTradeAddendumSpreadLeg

/-- Maturity Month Year: 5 bytes -/
structure MaturityMonthYear where
  year : BitVec 16
  month : BitVec 8
  day : BitVec 8
  week : BitVec 8
  deriving DecidableEq, Repr

namespace MaturityMonthYear

def encode (message : MaturityMonthYear) : List UInt8 :=
  encodeUIntLE 2 message.year
    ++ encodeUInt 1 message.month
    ++ encodeUInt 1 message.day
    ++ encodeUInt 1 message.week

def decode (bytes : List UInt8) : Option (MaturityMonthYear × List UInt8) := do
  let (year, bytes) ← decodeUIntLE 2 bytes
  let (month, bytes) ← decodeUInt 1 bytes
  let (day, bytes) ← decodeUInt 1 bytes
  let (week, bytes) ← decodeUInt 1 bytes
  pure ({ year, month, day, week }, bytes)

@[simp] theorem encode_length (message : MaturityMonthYear) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : MaturityMonthYear) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MaturityMonthYear) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end MaturityMonthYear

/-- Leg Option Delta: 5 bytes -/
structure LegOptionDelta where
  mantissa32 : BitVec 32
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace LegOptionDelta

def encode (message : LegOptionDelta) : List UInt8 :=
  encodeUIntLE 4 message.mantissa32
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (LegOptionDelta × List UInt8) := do
  let (mantissa32, bytes) ← decodeUIntLE 4 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa32, exponent }, bytes)

@[simp] theorem encode_length (message : LegOptionDelta) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : LegOptionDelta) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LegOptionDelta) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end LegOptionDelta

/-- Response Legs Group: 19 bytes -/
structure ResponseLegsGroup where
  legPrice : BitVec 64
  legOptionDelta : LegOptionDelta
  legSecurityId : BitVec 32
  legSide : BitVec 8
  legRatioQty : BitVec 8
  deriving DecidableEq, Repr

namespace ResponseLegsGroup

def encode (message : ResponseLegsGroup) : List UInt8 :=
  encodeUIntLE 8 message.legPrice
    ++ LegOptionDelta.encode message.legOptionDelta
    ++ encodeUIntLE 4 message.legSecurityId
    ++ encodeUInt 1 message.legSide
    ++ encodeUInt 1 message.legRatioQty

def decode (bytes : List UInt8) : Option (ResponseLegsGroup × List UInt8) := do
  let (legPrice, bytes) ← decodeUIntLE 8 bytes
  let (legOptionDelta, bytes) ← LegOptionDelta.decode bytes
  let (legSecurityId, bytes) ← decodeUIntLE 4 bytes
  let (legSide, bytes) ← decodeUInt 1 bytes
  let (legRatioQty, bytes) ← decodeUInt 1 bytes
  pure ({ legPrice, legOptionDelta, legSecurityId, legSide, legRatioQty }, bytes)

@[simp] theorem encode_length (message : ResponseLegsGroup) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, LegOptionDelta.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ResponseLegsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ResponseLegsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [LegOptionDelta.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end ResponseLegsGroup

/-- Response Legs Groups -/
structure ResponseLegsGroups where
  blockLength : BitVec 16
  responseLegsGroup : Bounded 1 ResponseLegsGroup
  deriving DecidableEq, Repr

namespace ResponseLegsGroups

def encode (message : ResponseLegsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.responseLegsGroup.val.length)
    ++ encodeMany ResponseLegsGroup.encode message.responseLegsGroup.val

def decode (bytes : List UInt8) : Option (ResponseLegsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (responseLegsGroup_, bytes) ← decodeMany ResponseLegsGroup.decode numInGroup.toNat bytes
  if fits_responseLegsGroup : responseLegsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, responseLegsGroup := ⟨responseLegsGroup_, fits_responseLegsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : ResponseLegsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ResponseLegsGroups) : (encode message).length ≤ 4848 := by
  have bound_responseLegsGroup := message.responseLegsGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const ResponseLegsGroup.encode 19 ResponseLegsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : ResponseLegsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 ResponseLegsGroup.encode ResponseLegsGroup.decode ResponseLegsGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.responseLegsGroup.length_lt, ↓reduceDIte]
  rfl

end ResponseLegsGroups

/-- Security Definition Response -/
structure SecurityDefinitionResponse where
  seqNum : BitVec 32
  uuid : BitVec 64
  text : Alpha 256
  financialInstrumentFullName : Alpha 35
  senderId : Alpha 20
  symbol : Alpha 20
  partyDetailsListReqId : BitVec 64
  securityReqId : BitVec 64
  securityResponseId : BitVec 64
  sendingTimeEpoch : BitVec 64
  securityGroup : Alpha 6
  securityType : Alpha 6
  location : Alpha 5
  securityIdOptional : BitVec 32
  currency : Alpha 3
  maturityMonthYear : MaturityMonthYear
  delayDuration : BitVec 16
  startDate : BitVec 16
  endDate : BitVec 16
  maxNoOfSubstitutions : BitVec 8
  sourceRepoId : BitVec 32
  terminationType : Alpha 8
  securityResponseType : BitVec 8
  expirationCycle : BitVec 8
  manualOrderIndicator : BitVec 8
  splitMsg : BitVec 8
  autoQuoteRequest : BitVec 8
  possRetransFlag : BitVec 8
  responseLegsGroups : ResponseLegsGroups
  deriving DecidableEq, Repr

namespace SecurityDefinitionResponse

def encode (message : SecurityDefinitionResponse) : List UInt8 :=
  encodeUIntLE 4 message.seqNum
    ++ encodeUIntLE 8 message.uuid
    ++ Alpha.encode message.text
    ++ Alpha.encode message.financialInstrumentFullName
    ++ Alpha.encode message.senderId
    ++ Alpha.encode message.symbol
    ++ encodeUIntLE 8 message.partyDetailsListReqId
    ++ encodeUIntLE 8 message.securityReqId
    ++ encodeUIntLE 8 message.securityResponseId
    ++ encodeUIntLE 8 message.sendingTimeEpoch
    ++ Alpha.encode message.securityGroup
    ++ Alpha.encode message.securityType
    ++ Alpha.encode message.location
    ++ encodeUIntLE 4 message.securityIdOptional
    ++ Alpha.encode message.currency
    ++ MaturityMonthYear.encode message.maturityMonthYear
    ++ encodeUIntLE 2 message.delayDuration
    ++ encodeUIntLE 2 message.startDate
    ++ encodeUIntLE 2 message.endDate
    ++ encodeUInt 1 message.maxNoOfSubstitutions
    ++ encodeUIntLE 4 message.sourceRepoId
    ++ Alpha.encode message.terminationType
    ++ encodeUInt 1 message.securityResponseType
    ++ encodeUInt 1 message.expirationCycle
    ++ encodeUInt 1 message.manualOrderIndicator
    ++ encodeUInt 1 message.splitMsg
    ++ encodeUInt 1 message.autoQuoteRequest
    ++ encodeUInt 1 message.possRetransFlag
    ++ ResponseLegsGroups.encode message.responseLegsGroups

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SecurityDefinitionResponse × List UInt8) := do
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (uuid, bytes) ← decodeUIntLE 8 bytes
  let (text, bytes) ← Alpha.decode 256 bytes
  let (financialInstrumentFullName, bytes) ← Alpha.decode 35 bytes
  let (senderId, bytes) ← Alpha.decode 20 bytes
  let (symbol, bytes) ← Alpha.decode 20 bytes
  let (partyDetailsListReqId, bytes) ← decodeUIntLE 8 bytes
  let (securityReqId, bytes) ← decodeUIntLE 8 bytes
  let (securityResponseId, bytes) ← decodeUIntLE 8 bytes
  let (sendingTimeEpoch, bytes) ← decodeUIntLE 8 bytes
  let (securityGroup, bytes) ← Alpha.decode 6 bytes
  let (securityType, bytes) ← Alpha.decode 6 bytes
  let (location, bytes) ← Alpha.decode 5 bytes
  let (securityIdOptional, bytes) ← decodeUIntLE 4 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (maturityMonthYear, bytes) ← MaturityMonthYear.decode bytes
  let (delayDuration, bytes) ← decodeUIntLE 2 bytes
  let (startDate, bytes) ← decodeUIntLE 2 bytes
  let (endDate, bytes) ← decodeUIntLE 2 bytes
  let (maxNoOfSubstitutions, bytes) ← decodeUInt 1 bytes
  let (sourceRepoId, bytes) ← decodeUIntLE 4 bytes
  let (terminationType, bytes) ← Alpha.decode 8 bytes
  let (securityResponseType, bytes) ← decodeUInt 1 bytes
  let (expirationCycle, bytes) ← decodeUInt 1 bytes
  let (manualOrderIndicator, bytes) ← decodeUInt 1 bytes
  let (splitMsg, bytes) ← decodeUInt 1 bytes
  let (autoQuoteRequest, bytes) ← decodeUInt 1 bytes
  let (possRetransFlag, bytes) ← decodeUInt 1 bytes
  let (responseLegsGroups, bytes) ← ResponseLegsGroups.decode bytes
  pure ({ seqNum, uuid, text, financialInstrumentFullName, senderId, symbol, partyDetailsListReqId, securityReqId, securityResponseId, sendingTimeEpoch, securityGroup, securityType, location, securityIdOptional, currency, maturityMonthYear, delayDuration, startDate, endDate, maxNoOfSubstitutions, sourceRepoId, terminationType, securityResponseType, expirationCycle, manualOrderIndicator, splitMsg, autoQuoteRequest, possRetransFlag, responseLegsGroups }, bytes)

theorem encode_length_pos (message : SecurityDefinitionResponse) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SecurityDefinitionResponse) : (encode message).length ≤ 5277 := by
  have bound_responseLegsGroups := ResponseLegsGroups.encode_length_le message.responseLegsGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, MaturityMonthYear.encode_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : SecurityDefinitionResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [MaturityMonthYear.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [ResponseLegsGroups.decode_encode, Option.bind_some]
  rfl

end SecurityDefinitionResponse

/-- Affected Orders Group: 32 bytes -/
structure AffectedOrdersGroup where
  origclordid : Alpha 20
  affectedOrderId : BitVec 64
  cxlQuantity : BitVec 32
  deriving DecidableEq, Repr

namespace AffectedOrdersGroup

def encode (message : AffectedOrdersGroup) : List UInt8 :=
  Alpha.encode message.origclordid
    ++ encodeUIntLE 8 message.affectedOrderId
    ++ encodeUIntLE 4 message.cxlQuantity

def decode (bytes : List UInt8) : Option (AffectedOrdersGroup × List UInt8) := do
  let (origclordid, bytes) ← Alpha.decode 20 bytes
  let (affectedOrderId, bytes) ← decodeUIntLE 8 bytes
  let (cxlQuantity, bytes) ← decodeUIntLE 4 bytes
  pure ({ origclordid, affectedOrderId, cxlQuantity }, bytes)

@[simp] theorem encode_length (message : AffectedOrdersGroup) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : AffectedOrdersGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AffectedOrdersGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end AffectedOrdersGroup

/-- Affected Orders Groups -/
structure AffectedOrdersGroups where
  blockLength : BitVec 16
  affectedOrdersGroup : Bounded 1 AffectedOrdersGroup
  deriving DecidableEq, Repr

namespace AffectedOrdersGroups

def encode (message : AffectedOrdersGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.affectedOrdersGroup.val.length)
    ++ encodeMany AffectedOrdersGroup.encode message.affectedOrdersGroup.val

def decode (bytes : List UInt8) : Option (AffectedOrdersGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (affectedOrdersGroup_, bytes) ← decodeMany AffectedOrdersGroup.decode numInGroup.toNat bytes
  if fits_affectedOrdersGroup : affectedOrdersGroup_.length < 256 ^ 1 then
    pure ({ blockLength, affectedOrdersGroup := ⟨affectedOrdersGroup_, fits_affectedOrdersGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : AffectedOrdersGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : AffectedOrdersGroups) : (encode message).length ≤ 8163 := by
  have bound_affectedOrdersGroup := message.affectedOrdersGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const AffectedOrdersGroup.encode 32 AffectedOrdersGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : AffectedOrdersGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 AffectedOrdersGroup.encode AffectedOrdersGroup.decode AffectedOrdersGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.affectedOrdersGroup.length_lt, ↓reduceDIte]
  rfl

end AffectedOrdersGroups

/-- Order Mass Action Report -/
structure OrderMassActionReport where
  seqNum : BitVec 32
  uuid : BitVec 64
  senderId : Alpha 20
  partyDetailsListReqId : BitVec 64
  transactTime : BitVec 64
  sendingTimeEpoch : BitVec 64
  orderRequestId : BitVec 64
  massActionReportId : BitVec 64
  securityGroup : Alpha 6
  location : Alpha 5
  securityIdOptional : BitVec 32
  delayDuration : BitVec 16
  massActionResponse : BitVec 8
  manualOrderIndicator : BitVec 8
  massActionScope : BitVec 8
  totalAffectedOrders : BitVec 32
  lastFragment : BitVec 8
  massActionRejectReason : BitVec 8
  marketSegmentId : BitVec 8
  massCancelRequestType : BitVec 8
  sideOptional : BitVec 8
  massActionOrdTyp : MassActionOrdTyp
  massCancelTif : BitVec 8
  splitMsg : BitVec 8
  liquidityFlag : BitVec 8
  possRetransFlag : BitVec 8
  delayToTime : BitVec 64
  affectedOrdersGroups : AffectedOrdersGroups
  deriving DecidableEq, Repr

namespace OrderMassActionReport

def encode (message : OrderMassActionReport) : List UInt8 :=
  encodeUIntLE 4 message.seqNum
    ++ encodeUIntLE 8 message.uuid
    ++ Alpha.encode message.senderId
    ++ encodeUIntLE 8 message.partyDetailsListReqId
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.sendingTimeEpoch
    ++ encodeUIntLE 8 message.orderRequestId
    ++ encodeUIntLE 8 message.massActionReportId
    ++ Alpha.encode message.securityGroup
    ++ Alpha.encode message.location
    ++ encodeUIntLE 4 message.securityIdOptional
    ++ encodeUIntLE 2 message.delayDuration
    ++ encodeUInt 1 message.massActionResponse
    ++ encodeUInt 1 message.manualOrderIndicator
    ++ encodeUInt 1 message.massActionScope
    ++ encodeUIntLE 4 message.totalAffectedOrders
    ++ encodeUInt 1 message.lastFragment
    ++ encodeUInt 1 message.massActionRejectReason
    ++ encodeUInt 1 message.marketSegmentId
    ++ encodeUInt 1 message.massCancelRequestType
    ++ encodeUInt 1 message.sideOptional
    ++ MassActionOrdTyp.encode message.massActionOrdTyp
    ++ encodeUInt 1 message.massCancelTif
    ++ encodeUInt 1 message.splitMsg
    ++ encodeUInt 1 message.liquidityFlag
    ++ encodeUInt 1 message.possRetransFlag
    ++ encodeUIntLE 8 message.delayToTime
    ++ AffectedOrdersGroups.encode message.affectedOrdersGroups

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderMassActionReport × List UInt8) := do
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (uuid, bytes) ← decodeUIntLE 8 bytes
  let (senderId, bytes) ← Alpha.decode 20 bytes
  let (partyDetailsListReqId, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (sendingTimeEpoch, bytes) ← decodeUIntLE 8 bytes
  let (orderRequestId, bytes) ← decodeUIntLE 8 bytes
  let (massActionReportId, bytes) ← decodeUIntLE 8 bytes
  let (securityGroup, bytes) ← Alpha.decode 6 bytes
  let (location, bytes) ← Alpha.decode 5 bytes
  let (securityIdOptional, bytes) ← decodeUIntLE 4 bytes
  let (delayDuration, bytes) ← decodeUIntLE 2 bytes
  let (massActionResponse, bytes) ← decodeUInt 1 bytes
  let (manualOrderIndicator, bytes) ← decodeUInt 1 bytes
  let (massActionScope, bytes) ← decodeUInt 1 bytes
  let (totalAffectedOrders, bytes) ← decodeUIntLE 4 bytes
  let (lastFragment, bytes) ← decodeUInt 1 bytes
  let (massActionRejectReason, bytes) ← decodeUInt 1 bytes
  let (marketSegmentId, bytes) ← decodeUInt 1 bytes
  let (massCancelRequestType, bytes) ← decodeUInt 1 bytes
  let (sideOptional, bytes) ← decodeUInt 1 bytes
  let (massActionOrdTyp, bytes) ← MassActionOrdTyp.decode bytes
  let (massCancelTif, bytes) ← decodeUInt 1 bytes
  let (splitMsg, bytes) ← decodeUInt 1 bytes
  let (liquidityFlag, bytes) ← decodeUInt 1 bytes
  let (possRetransFlag, bytes) ← decodeUInt 1 bytes
  let (delayToTime, bytes) ← decodeUIntLE 8 bytes
  let (affectedOrdersGroups, bytes) ← AffectedOrdersGroups.decode bytes
  pure ({ seqNum, uuid, senderId, partyDetailsListReqId, transactTime, sendingTimeEpoch, orderRequestId, massActionReportId, securityGroup, location, securityIdOptional, delayDuration, massActionResponse, manualOrderIndicator, massActionScope, totalAffectedOrders, lastFragment, massActionRejectReason, marketSegmentId, massCancelRequestType, sideOptional, massActionOrdTyp, massCancelTif, splitMsg, liquidityFlag, possRetransFlag, delayToTime, affectedOrdersGroups }, bytes)

theorem encode_length_pos (message : OrderMassActionReport) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderMassActionReport) : (encode message).length ≤ 8277 := by
  have bound_affectedOrdersGroups := AffectedOrdersGroups.encode_length_le message.affectedOrdersGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length, MassActionOrdTyp.encode_length]
  omega

@[simp] theorem decode_encode (message : OrderMassActionReport) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [MassActionOrdTyp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [AffectedOrdersGroups.decode_encode, Option.bind_some]
  rfl

end OrderMassActionReport

/-- Quote Cancel Ack Entries Group: 9 bytes -/
structure QuoteCancelAckEntriesGroup where
  quoteEntryId : BitVec 32
  securityId : BitVec 32
  quoteEntryRejectReason : BitVec 8
  deriving DecidableEq, Repr

namespace QuoteCancelAckEntriesGroup

def encode (message : QuoteCancelAckEntriesGroup) : List UInt8 :=
  encodeUIntLE 4 message.quoteEntryId
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUInt 1 message.quoteEntryRejectReason

def decode (bytes : List UInt8) : Option (QuoteCancelAckEntriesGroup × List UInt8) := do
  let (quoteEntryId, bytes) ← decodeUIntLE 4 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (quoteEntryRejectReason, bytes) ← decodeUInt 1 bytes
  pure ({ quoteEntryId, securityId, quoteEntryRejectReason }, bytes)

@[simp] theorem encode_length (message : QuoteCancelAckEntriesGroup) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : QuoteCancelAckEntriesGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteCancelAckEntriesGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end QuoteCancelAckEntriesGroup

/-- Quote Cancel Ack Entries Groups -/
structure QuoteCancelAckEntriesGroups where
  blockLength : BitVec 16
  quoteCancelAckEntriesGroup : Bounded 1 QuoteCancelAckEntriesGroup
  deriving DecidableEq, Repr

namespace QuoteCancelAckEntriesGroups

def encode (message : QuoteCancelAckEntriesGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.quoteCancelAckEntriesGroup.val.length)
    ++ encodeMany QuoteCancelAckEntriesGroup.encode message.quoteCancelAckEntriesGroup.val

def decode (bytes : List UInt8) : Option (QuoteCancelAckEntriesGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (quoteCancelAckEntriesGroup_, bytes) ← decodeMany QuoteCancelAckEntriesGroup.decode numInGroup.toNat bytes
  if fits_quoteCancelAckEntriesGroup : quoteCancelAckEntriesGroup_.length < 256 ^ 1 then
    pure ({ blockLength, quoteCancelAckEntriesGroup := ⟨quoteCancelAckEntriesGroup_, fits_quoteCancelAckEntriesGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : QuoteCancelAckEntriesGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : QuoteCancelAckEntriesGroups) : (encode message).length ≤ 2298 := by
  have bound_quoteCancelAckEntriesGroup := message.quoteCancelAckEntriesGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const QuoteCancelAckEntriesGroup.encode 9 QuoteCancelAckEntriesGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : QuoteCancelAckEntriesGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 QuoteCancelAckEntriesGroup.encode QuoteCancelAckEntriesGroup.decode QuoteCancelAckEntriesGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.quoteCancelAckEntriesGroup.length_lt, ↓reduceDIte]
  rfl

end QuoteCancelAckEntriesGroups

/-- Quote Cancel Ack Sets Group: 4 bytes -/
structure QuoteCancelAckSetsGroup where
  quoteSetId : BitVec 16
  quoteErrorCode : BitVec 16
  deriving DecidableEq, Repr

namespace QuoteCancelAckSetsGroup

def encode (message : QuoteCancelAckSetsGroup) : List UInt8 :=
  encodeUIntLE 2 message.quoteSetId
    ++ encodeUIntLE 2 message.quoteErrorCode

def decode (bytes : List UInt8) : Option (QuoteCancelAckSetsGroup × List UInt8) := do
  let (quoteSetId, bytes) ← decodeUIntLE 2 bytes
  let (quoteErrorCode, bytes) ← decodeUIntLE 2 bytes
  pure ({ quoteSetId, quoteErrorCode }, bytes)

@[simp] theorem encode_length (message : QuoteCancelAckSetsGroup) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : QuoteCancelAckSetsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteCancelAckSetsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end QuoteCancelAckSetsGroup

/-- Quote Cancel Ack Sets Groups -/
structure QuoteCancelAckSetsGroups where
  blockLength : BitVec 16
  quoteCancelAckSetsGroup : Bounded 1 QuoteCancelAckSetsGroup
  deriving DecidableEq, Repr

namespace QuoteCancelAckSetsGroups

def encode (message : QuoteCancelAckSetsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.quoteCancelAckSetsGroup.val.length)
    ++ encodeMany QuoteCancelAckSetsGroup.encode message.quoteCancelAckSetsGroup.val

def decode (bytes : List UInt8) : Option (QuoteCancelAckSetsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (quoteCancelAckSetsGroup_, bytes) ← decodeMany QuoteCancelAckSetsGroup.decode numInGroup.toNat bytes
  if fits_quoteCancelAckSetsGroup : quoteCancelAckSetsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, quoteCancelAckSetsGroup := ⟨quoteCancelAckSetsGroup_, fits_quoteCancelAckSetsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : QuoteCancelAckSetsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : QuoteCancelAckSetsGroups) : (encode message).length ≤ 1023 := by
  have bound_quoteCancelAckSetsGroup := message.quoteCancelAckSetsGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const QuoteCancelAckSetsGroup.encode 4 QuoteCancelAckSetsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : QuoteCancelAckSetsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 QuoteCancelAckSetsGroup.encode QuoteCancelAckSetsGroup.decode QuoteCancelAckSetsGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.quoteCancelAckSetsGroup.length_lt, ↓reduceDIte]
  rfl

end QuoteCancelAckSetsGroups

/-- Quote Cancel Ack -/
structure QuoteCancelAck where
  seqNum : BitVec 32
  uuid : BitVec 64
  text : Alpha 256
  senderId : Alpha 20
  partyDetailsListReqId : BitVec 64
  requestTime : BitVec 64
  sendingTimeEpoch : BitVec 64
  cancelledSymbol : Alpha 6
  location : Alpha 5
  quoteId : BitVec 32
  quoteRejectReason : BitVec 16
  delayDuration : BitVec 16
  manualOrderIndicator : BitVec 8
  quoteCxlStatus : BitVec 8
  noProcessedEntries : BitVec 32
  mmProtectionReset : BitVec 8
  unsolicitedCancelType : Alpha 1
  splitMsg : BitVec 8
  totNoQuoteEntriesOptional : BitVec 8
  liquidityFlag : BitVec 8
  possRetransFlag : BitVec 8
  delayToTime : BitVec 64
  quoteCancelAckEntriesGroups : QuoteCancelAckEntriesGroups
  quoteCancelAckSetsGroups : QuoteCancelAckSetsGroups
  deriving DecidableEq, Repr

namespace QuoteCancelAck

def encode (message : QuoteCancelAck) : List UInt8 :=
  encodeUIntLE 4 message.seqNum
    ++ encodeUIntLE 8 message.uuid
    ++ Alpha.encode message.text
    ++ Alpha.encode message.senderId
    ++ encodeUIntLE 8 message.partyDetailsListReqId
    ++ encodeUIntLE 8 message.requestTime
    ++ encodeUIntLE 8 message.sendingTimeEpoch
    ++ Alpha.encode message.cancelledSymbol
    ++ Alpha.encode message.location
    ++ encodeUIntLE 4 message.quoteId
    ++ encodeUIntLE 2 message.quoteRejectReason
    ++ encodeUIntLE 2 message.delayDuration
    ++ encodeUInt 1 message.manualOrderIndicator
    ++ encodeUInt 1 message.quoteCxlStatus
    ++ encodeUIntLE 4 message.noProcessedEntries
    ++ encodeUInt 1 message.mmProtectionReset
    ++ Alpha.encode message.unsolicitedCancelType
    ++ encodeUInt 1 message.splitMsg
    ++ encodeUInt 1 message.totNoQuoteEntriesOptional
    ++ encodeUInt 1 message.liquidityFlag
    ++ encodeUInt 1 message.possRetransFlag
    ++ encodeUIntLE 8 message.delayToTime
    ++ QuoteCancelAckEntriesGroups.encode message.quoteCancelAckEntriesGroups
    ++ QuoteCancelAckSetsGroups.encode message.quoteCancelAckSetsGroups

def decode (bytes : List UInt8) : Option (QuoteCancelAck × List UInt8) := do
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (uuid, bytes) ← decodeUIntLE 8 bytes
  let (text, bytes) ← Alpha.decode 256 bytes
  let (senderId, bytes) ← Alpha.decode 20 bytes
  let (partyDetailsListReqId, bytes) ← decodeUIntLE 8 bytes
  let (requestTime, bytes) ← decodeUIntLE 8 bytes
  let (sendingTimeEpoch, bytes) ← decodeUIntLE 8 bytes
  let (cancelledSymbol, bytes) ← Alpha.decode 6 bytes
  let (location, bytes) ← Alpha.decode 5 bytes
  let (quoteId, bytes) ← decodeUIntLE 4 bytes
  let (quoteRejectReason, bytes) ← decodeUIntLE 2 bytes
  let (delayDuration, bytes) ← decodeUIntLE 2 bytes
  let (manualOrderIndicator, bytes) ← decodeUInt 1 bytes
  let (quoteCxlStatus, bytes) ← decodeUInt 1 bytes
  let (noProcessedEntries, bytes) ← decodeUIntLE 4 bytes
  let (mmProtectionReset, bytes) ← decodeUInt 1 bytes
  let (unsolicitedCancelType, bytes) ← Alpha.decode 1 bytes
  let (splitMsg, bytes) ← decodeUInt 1 bytes
  let (totNoQuoteEntriesOptional, bytes) ← decodeUInt 1 bytes
  let (liquidityFlag, bytes) ← decodeUInt 1 bytes
  let (possRetransFlag, bytes) ← decodeUInt 1 bytes
  let (delayToTime, bytes) ← decodeUIntLE 8 bytes
  let (quoteCancelAckEntriesGroups, bytes) ← QuoteCancelAckEntriesGroups.decode bytes
  let (quoteCancelAckSetsGroups, bytes) ← QuoteCancelAckSetsGroups.decode bytes
  pure ({ seqNum, uuid, text, senderId, partyDetailsListReqId, requestTime, sendingTimeEpoch, cancelledSymbol, location, quoteId, quoteRejectReason, delayDuration, manualOrderIndicator, quoteCxlStatus, noProcessedEntries, mmProtectionReset, unsolicitedCancelType, splitMsg, totNoQuoteEntriesOptional, liquidityFlag, possRetransFlag, delayToTime, quoteCancelAckEntriesGroups, quoteCancelAckSetsGroups }, bytes)

theorem encode_length_pos (message : QuoteCancelAck) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : QuoteCancelAck) : (encode message).length ≤ 3672 := by
  have bound_quoteCancelAckEntriesGroups := QuoteCancelAckEntriesGroups.encode_length_le message.quoteCancelAckEntriesGroups
  have bound_quoteCancelAckSetsGroups := QuoteCancelAckSetsGroups.encode_length_le message.quoteCancelAckSetsGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : QuoteCancelAck) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [QuoteCancelAckEntriesGroups.decode_encode]
  simp only [Option.bind_some]
  rw [QuoteCancelAckSetsGroups.decode_encode, Option.bind_some]
  rfl

end QuoteCancelAck

/-- Any Server Payload, selected by Template Id -/
inductive ServerPayload where
  | negotiationResponse (message : NegotiationResponse) -- 501
  | negotiationReject (message : NegotiationReject) -- 502
  | establishmentAck (message : EstablishmentAck) -- 504
  | establishmentReject (message : EstablishmentReject) -- 505
  | sequence (message : Sequence) -- 506
  | terminate (message : Terminate) -- 507
  | retransmission (message : Retransmission) -- 509
  | retransmitReject (message : RetransmitReject) -- 510
  | notApplied (message : NotApplied) -- 513
  | partyDetailsDefinitionRequestAck (message : PartyDetailsDefinitionRequestAck) -- 519
  | businessReject (message : BusinessReject) -- 521
  | executionReportNew (message : ExecutionReportNew) -- 522
  | executionReportReject (message : ExecutionReportReject) -- 523
  | executionReportElimination (message : ExecutionReportElimination) -- 524
  | executionReportTradeOutright (message : ExecutionReportTradeOutright) -- 525
  | executionReportTradeSpread (message : ExecutionReportTradeSpread) -- 526
  | executionReportTradeSpreadLeg (message : ExecutionReportTradeSpreadLeg) -- 527
  | executionReportModify (message : ExecutionReportModify) -- 531
  | executionReportStatus (message : ExecutionReportStatus) -- 532
  | executionReportCancel (message : ExecutionReportCancel) -- 534
  | orderCancelReject (message : OrderCancelReject) -- 535
  | orderCancelReplaceReject (message : OrderCancelReplaceReject) -- 536
  | partyDetailsListReport (message : PartyDetailsListReport) -- 538
  | executionAck (message : ExecutionAck) -- 539
  | massQuoteAck (message : MassQuoteAck) -- 545
  | requestForQuoteAck (message : RequestForQuoteAck) -- 546
  | executionReportTradeAddendumOutright (message : ExecutionReportTradeAddendumOutright) -- 548
  | executionReportTradeAddendumSpread (message : ExecutionReportTradeAddendumSpread) -- 549
  | executionReportTradeAddendumSpreadLeg (message : ExecutionReportTradeAddendumSpreadLeg) -- 550
  | securityDefinitionResponse (message : SecurityDefinitionResponse) -- 561
  | orderMassActionReport (message : OrderMassActionReport) -- 562
  | quoteCancelAck (message : QuoteCancelAck) -- 563
  deriving DecidableEq, Repr

namespace ServerPayload

/-- The Template Id each message is sent under -/
def tag : ServerPayload → BitVec 16
  | .negotiationResponse _ => 501
  | .negotiationReject _ => 502
  | .establishmentAck _ => 504
  | .establishmentReject _ => 505
  | .sequence _ => 506
  | .terminate _ => 507
  | .retransmission _ => 509
  | .retransmitReject _ => 510
  | .notApplied _ => 513
  | .partyDetailsDefinitionRequestAck _ => 519
  | .businessReject _ => 521
  | .executionReportNew _ => 522
  | .executionReportReject _ => 523
  | .executionReportElimination _ => 524
  | .executionReportTradeOutright _ => 525
  | .executionReportTradeSpread _ => 526
  | .executionReportTradeSpreadLeg _ => 527
  | .executionReportModify _ => 531
  | .executionReportStatus _ => 532
  | .executionReportCancel _ => 534
  | .orderCancelReject _ => 535
  | .orderCancelReplaceReject _ => 536
  | .partyDetailsListReport _ => 538
  | .executionAck _ => 539
  | .massQuoteAck _ => 545
  | .requestForQuoteAck _ => 546
  | .executionReportTradeAddendumOutright _ => 548
  | .executionReportTradeAddendumSpread _ => 549
  | .executionReportTradeAddendumSpreadLeg _ => 550
  | .securityDefinitionResponse _ => 561
  | .orderMassActionReport _ => 562
  | .quoteCancelAck _ => 563

def encode : ServerPayload → List UInt8
  | .negotiationResponse message => NegotiationResponse.encode message
  | .negotiationReject message => NegotiationReject.encode message
  | .establishmentAck message => EstablishmentAck.encode message
  | .establishmentReject message => EstablishmentReject.encode message
  | .sequence message => Sequence.encode message
  | .terminate message => Terminate.encode message
  | .retransmission message => Retransmission.encode message
  | .retransmitReject message => RetransmitReject.encode message
  | .notApplied message => NotApplied.encode message
  | .partyDetailsDefinitionRequestAck message => PartyDetailsDefinitionRequestAck.encode message
  | .businessReject message => BusinessReject.encode message
  | .executionReportNew message => ExecutionReportNew.encode message
  | .executionReportReject message => ExecutionReportReject.encode message
  | .executionReportElimination message => ExecutionReportElimination.encode message
  | .executionReportTradeOutright message => ExecutionReportTradeOutright.encode message
  | .executionReportTradeSpread message => ExecutionReportTradeSpread.encode message
  | .executionReportTradeSpreadLeg message => ExecutionReportTradeSpreadLeg.encode message
  | .executionReportModify message => ExecutionReportModify.encode message
  | .executionReportStatus message => ExecutionReportStatus.encode message
  | .executionReportCancel message => ExecutionReportCancel.encode message
  | .orderCancelReject message => OrderCancelReject.encode message
  | .orderCancelReplaceReject message => OrderCancelReplaceReject.encode message
  | .partyDetailsListReport message => PartyDetailsListReport.encode message
  | .executionAck message => ExecutionAck.encode message
  | .massQuoteAck message => MassQuoteAck.encode message
  | .requestForQuoteAck message => RequestForQuoteAck.encode message
  | .executionReportTradeAddendumOutright message => ExecutionReportTradeAddendumOutright.encode message
  | .executionReportTradeAddendumSpread message => ExecutionReportTradeAddendumSpread.encode message
  | .executionReportTradeAddendumSpreadLeg message => ExecutionReportTradeAddendumSpreadLeg.encode message
  | .securityDefinitionResponse message => SecurityDefinitionResponse.encode message
  | .orderMassActionReport message => OrderMassActionReport.encode message
  | .quoteCancelAck message => QuoteCancelAck.encode message

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (ServerPayload × List UInt8) :=
  if tag = 501 then (NegotiationResponse.decode bytes).map fun (message, rest) => (.negotiationResponse message, rest)
  else if tag = 502 then (NegotiationReject.decode bytes).map fun (message, rest) => (.negotiationReject message, rest)
  else if tag = 504 then (EstablishmentAck.decode bytes).map fun (message, rest) => (.establishmentAck message, rest)
  else if tag = 505 then (EstablishmentReject.decode bytes).map fun (message, rest) => (.establishmentReject message, rest)
  else if tag = 506 then (Sequence.decode bytes).map fun (message, rest) => (.sequence message, rest)
  else if tag = 507 then (Terminate.decode bytes).map fun (message, rest) => (.terminate message, rest)
  else if tag = 509 then (Retransmission.decode bytes).map fun (message, rest) => (.retransmission message, rest)
  else if tag = 510 then (RetransmitReject.decode bytes).map fun (message, rest) => (.retransmitReject message, rest)
  else if tag = 513 then (NotApplied.decode bytes).map fun (message, rest) => (.notApplied message, rest)
  else if tag = 519 then (PartyDetailsDefinitionRequestAck.decode bytes).map fun (message, rest) => (.partyDetailsDefinitionRequestAck message, rest)
  else if tag = 521 then (BusinessReject.decode bytes).map fun (message, rest) => (.businessReject message, rest)
  else if tag = 522 then (ExecutionReportNew.decode bytes).map fun (message, rest) => (.executionReportNew message, rest)
  else if tag = 523 then (ExecutionReportReject.decode bytes).map fun (message, rest) => (.executionReportReject message, rest)
  else if tag = 524 then (ExecutionReportElimination.decode bytes).map fun (message, rest) => (.executionReportElimination message, rest)
  else if tag = 525 then (ExecutionReportTradeOutright.decode bytes).map fun (message, rest) => (.executionReportTradeOutright message, rest)
  else if tag = 526 then (ExecutionReportTradeSpread.decode bytes).map fun (message, rest) => (.executionReportTradeSpread message, rest)
  else if tag = 527 then (ExecutionReportTradeSpreadLeg.decode bytes).map fun (message, rest) => (.executionReportTradeSpreadLeg message, rest)
  else if tag = 531 then (ExecutionReportModify.decode bytes).map fun (message, rest) => (.executionReportModify message, rest)
  else if tag = 532 then (ExecutionReportStatus.decode bytes).map fun (message, rest) => (.executionReportStatus message, rest)
  else if tag = 534 then (ExecutionReportCancel.decode bytes).map fun (message, rest) => (.executionReportCancel message, rest)
  else if tag = 535 then (OrderCancelReject.decode bytes).map fun (message, rest) => (.orderCancelReject message, rest)
  else if tag = 536 then (OrderCancelReplaceReject.decode bytes).map fun (message, rest) => (.orderCancelReplaceReject message, rest)
  else if tag = 538 then (PartyDetailsListReport.decode bytes).map fun (message, rest) => (.partyDetailsListReport message, rest)
  else if tag = 539 then (ExecutionAck.decode bytes).map fun (message, rest) => (.executionAck message, rest)
  else if tag = 545 then (MassQuoteAck.decode bytes).map fun (message, rest) => (.massQuoteAck message, rest)
  else if tag = 546 then (RequestForQuoteAck.decode bytes).map fun (message, rest) => (.requestForQuoteAck message, rest)
  else if tag = 548 then (ExecutionReportTradeAddendumOutright.decode bytes).map fun (message, rest) => (.executionReportTradeAddendumOutright message, rest)
  else if tag = 549 then (ExecutionReportTradeAddendumSpread.decode bytes).map fun (message, rest) => (.executionReportTradeAddendumSpread message, rest)
  else if tag = 550 then (ExecutionReportTradeAddendumSpreadLeg.decode bytes).map fun (message, rest) => (.executionReportTradeAddendumSpreadLeg message, rest)
  else if tag = 561 then (SecurityDefinitionResponse.decode bytes).map fun (message, rest) => (.securityDefinitionResponse message, rest)
  else if tag = 562 then (OrderMassActionReport.decode bytes).map fun (message, rest) => (.orderMassActionReport message, rest)
  else if tag = 563 then (QuoteCancelAck.decode bytes).map fun (message, rest) => (.quoteCancelAck message, rest)
  else none

@[simp] theorem decode_encode (message : ServerPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ServerPayload

/-- Server Simple Open Frame -/
structure ServerSimpleOpenFrame where
  encodingType : BitVec 16
  blockLength : BitVec 16
  schemaId : BitVec 16
  version : BitVec 16
  serverPayload : ServerPayload
  deriving DecidableEq, Repr

namespace ServerSimpleOpenFrame

def encodeBody (message : ServerSimpleOpenFrame) : List UInt8 :=
  encodeUIntLE 2 message.encodingType
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUIntLE 2 (ServerPayload.tag message.serverPayload)
    ++ encodeUIntLE 2 message.schemaId
    ++ encodeUIntLE 2 message.version
    ++ ServerPayload.encode message.serverPayload

def decodeBody (bytes : List UInt8) : Option (ServerSimpleOpenFrame × List UInt8) := do
  let (encodingType, bytes) ← decodeUIntLE 2 bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (templateId, bytes) ← decodeUIntLE 2 bytes
  let (schemaId, bytes) ← decodeUIntLE 2 bytes
  let (version, bytes) ← decodeUIntLE 2 bytes
  let (serverPayload, bytes) ← ServerPayload.decode templateId bytes
  pure ({ encodingType, blockLength, schemaId, version, serverPayload }, bytes)

theorem decodeBody_encodeBody (message : ServerSimpleOpenFrame) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [ServerPayload.decode_encode, Option.bind_some]
  rfl

/-- Size rule: Message Length counts the bytes after it plus 2, so it is written from the body; the body has no bound the prefix must fit, so it is read by its content and the prefix is not checked -/
def encode (message : ServerSimpleOpenFrame) : List UInt8 :=
  encodeUIntLE 2 (BitVec.ofNat (8 * 2) ((encodeBody message).length + 2))
    ++ encodeBody message

def decode (bytes : List UInt8) : Option (ServerSimpleOpenFrame × List UInt8) := do
  let (_, bytes) ← decodeUIntLE 2 bytes
  decodeBody bytes

@[simp] theorem decode_encode (message : ServerSimpleOpenFrame) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  exact decodeBody_encodeBody message rest

theorem encode_length_pos (message : ServerSimpleOpenFrame) : (encode message).length > 0 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]
  omega

end ServerSimpleOpenFrame

/-- Server Packet -/
structure ServerPacket where
  serverSimpleOpenFrame : List ServerSimpleOpenFrame
  deriving DecidableEq, Repr

namespace ServerPacket

def encode (message : ServerPacket) : List UInt8 :=
  encodeMany ServerSimpleOpenFrame.encode message.serverSimpleOpenFrame

def decode (bytes : List UInt8) : Option ServerPacket := do
  let serverSimpleOpenFrame ← decodeAll ServerSimpleOpenFrame.decode bytes.length bytes
  pure { serverSimpleOpenFrame }

theorem decode_encode (message : ServerPacket) : decode (encode message) = some message := by
  unfold decode encode
  simp only [Option.bind_eq_bind]
  rw [decodeAll_encodeMany ServerSimpleOpenFrame.encode ServerSimpleOpenFrame.decode ServerSimpleOpenFrame.decode_encode ServerSimpleOpenFrame.encode_length_pos message.serverSimpleOpenFrame _ (encodeMany_length_ge ServerSimpleOpenFrame.encode ServerSimpleOpenFrame.encode_length_pos message.serverSimpleOpenFrame), Option.bind_some]
  rfl

end ServerPacket

end Omi.CmeGlobexIlink3SbeV85Server
