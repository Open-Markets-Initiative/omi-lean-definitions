import Omi.Wire

/-!
# CME Group iLink 3 v8.9

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Exec Inst is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Client Simple Open Frame's Message Length is written from its body but not checked on decode, since the body has no bound the prefix must fit; the body is read by its content.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.CmeGlobexIlink3SbeV89Client

/-- Ord Type: one byte code -/
def OrdType.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x34, 0x4B]

inductive OrdType where
  | marketwithProtection -- Marketwith Protection
  | limit -- Limit
  | stopwithProtection -- Stopwith Protection
  | stopLimit -- Stop Limit
  | marketWithLeftoverAsLimit -- Market With Leftover As Limit
  | unlisted (byte : { byte : UInt8 // byte ∉ OrdType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrdType

def toByte : OrdType → UInt8
  | .marketwithProtection => 0x31
  | .limit => 0x32
  | .stopwithProtection => 0x33
  | .stopLimit => 0x34
  | .marketWithLeftoverAsLimit => 0x4B
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrdType :=
  if byte = 0x31 then .marketwithProtection
  else if byte = 0x32 then .limit
  else if byte = 0x33 then .stopwithProtection
  else if byte = 0x34 then .stopLimit
  else .marketWithLeftoverAsLimit

def ofByte (byte : UInt8) : OrdType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrdType) : ofByte value.toByte = value := by
  cases value with
  | marketwithProtection => decide
  | limit => decide
  | stopwithProtection => decide
  | stopLimit => decide
  | marketWithLeftoverAsLimit => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrdType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrdType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrdType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OrdType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrdType

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

/-- Cust Order Handling Inst: one byte code -/
def CustOrderHandlingInst.codes : List UInt8 :=
  [0x43, 0x44, 0x47, 0x48, 0x57, 0x59]

inductive CustOrderHandlingInst where
  | fcMprovidedscreen -- Fc Mprovidedscreen
  | otherprovidedscreen -- Otherprovidedscreen
  | fcmapIorFix -- Fcmap Ior Fix
  | algoEngine -- Algo Engine
  | deskElectronic -- Desk Electronic
  | clientElectronic -- Client Electronic
  | unlisted (byte : { byte : UInt8 // byte ∉ CustOrderHandlingInst.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CustOrderHandlingInst

def toByte : CustOrderHandlingInst → UInt8
  | .fcMprovidedscreen => 0x43
  | .otherprovidedscreen => 0x44
  | .fcmapIorFix => 0x47
  | .algoEngine => 0x48
  | .deskElectronic => 0x57
  | .clientElectronic => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CustOrderHandlingInst :=
  if byte = 0x43 then .fcMprovidedscreen
  else if byte = 0x44 then .otherprovidedscreen
  else if byte = 0x47 then .fcmapIorFix
  else if byte = 0x48 then .algoEngine
  else if byte = 0x57 then .deskElectronic
  else .clientElectronic

def ofByte (byte : UInt8) : CustOrderHandlingInst :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CustOrderHandlingInst) : ofByte value.toByte = value := by
  cases value with
  | fcMprovidedscreen => decide
  | otherprovidedscreen => decide
  | fcmapIorFix => decide
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

/-- Negotiate -/
structure Negotiate where
  hmacSignature : Alpha 32
  accessKeyId : Alpha 20
  uuid : BitVec 64
  requestTimestamp : BitVec 64
  session : Alpha 3
  firm : Alpha 5
  credentials : Credentials
  deriving DecidableEq, Repr

namespace Negotiate

def encode (message : Negotiate) : List UInt8 :=
  Alpha.encode message.hmacSignature
    ++ Alpha.encode message.accessKeyId
    ++ encodeUIntLE 8 message.uuid
    ++ encodeUIntLE 8 message.requestTimestamp
    ++ Alpha.encode message.session
    ++ Alpha.encode message.firm
    ++ Credentials.encode message.credentials

def decode (bytes : List UInt8) : Option (Negotiate × List UInt8) := do
  let (hmacSignature, bytes) ← Alpha.decode 32 bytes
  let (accessKeyId, bytes) ← Alpha.decode 20 bytes
  let (uuid, bytes) ← decodeUIntLE 8 bytes
  let (requestTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (session, bytes) ← Alpha.decode 3 bytes
  let (firm, bytes) ← Alpha.decode 5 bytes
  let (credentials, bytes) ← Credentials.decode bytes
  pure ({ hmacSignature, accessKeyId, uuid, requestTimestamp, session, firm, credentials }, bytes)

theorem encode_length_pos (message : Negotiate) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Negotiate) : (encode message).length ≤ 65613 := by
  have bound_credentials := Credentials.encode_length_le message.credentials
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]
  omega

@[simp] theorem decode_encode (message : Negotiate) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Credentials.decode_encode, Option.bind_some]
  rfl

end Negotiate

/-- Establish -/
structure Establish where
  hmacSignature : Alpha 32
  accessKeyId : Alpha 20
  tradingSystemName : Alpha 30
  tradingSystemVersion : Alpha 10
  tradingSystemVendor : Alpha 10
  uuid : BitVec 64
  requestTimestamp : BitVec 64
  nextSeqNo : BitVec 32
  session : Alpha 3
  firm : Alpha 5
  keepAliveInterval : BitVec 16
  credentials : Credentials
  deriving DecidableEq, Repr

namespace Establish

def encode (message : Establish) : List UInt8 :=
  Alpha.encode message.hmacSignature
    ++ Alpha.encode message.accessKeyId
    ++ Alpha.encode message.tradingSystemName
    ++ Alpha.encode message.tradingSystemVersion
    ++ Alpha.encode message.tradingSystemVendor
    ++ encodeUIntLE 8 message.uuid
    ++ encodeUIntLE 8 message.requestTimestamp
    ++ encodeUIntLE 4 message.nextSeqNo
    ++ Alpha.encode message.session
    ++ Alpha.encode message.firm
    ++ encodeUIntLE 2 message.keepAliveInterval
    ++ Credentials.encode message.credentials

def decode (bytes : List UInt8) : Option (Establish × List UInt8) := do
  let (hmacSignature, bytes) ← Alpha.decode 32 bytes
  let (accessKeyId, bytes) ← Alpha.decode 20 bytes
  let (tradingSystemName, bytes) ← Alpha.decode 30 bytes
  let (tradingSystemVersion, bytes) ← Alpha.decode 10 bytes
  let (tradingSystemVendor, bytes) ← Alpha.decode 10 bytes
  let (uuid, bytes) ← decodeUIntLE 8 bytes
  let (requestTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (nextSeqNo, bytes) ← decodeUIntLE 4 bytes
  let (session, bytes) ← Alpha.decode 3 bytes
  let (firm, bytes) ← Alpha.decode 5 bytes
  let (keepAliveInterval, bytes) ← decodeUIntLE 2 bytes
  let (credentials, bytes) ← Credentials.decode bytes
  pure ({ hmacSignature, accessKeyId, tradingSystemName, tradingSystemVersion, tradingSystemVendor, uuid, requestTimestamp, nextSeqNo, session, firm, keepAliveInterval, credentials }, bytes)

theorem encode_length_pos (message : Establish) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Establish) : (encode message).length ≤ 65669 := by
  have bound_credentials := Credentials.encode_length_le message.credentials
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]
  omega

@[simp] theorem decode_encode (message : Establish) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
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
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Credentials.decode_encode, Option.bind_some]
  rfl

end Establish

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

/-- Retransmit Request: 30 bytes -/
structure RetransmitRequest where
  uuid : BitVec 64
  lastUuid : BitVec 64
  requestTimestamp : BitVec 64
  fromSeqNo : BitVec 32
  msgCount16 : BitVec 16
  deriving DecidableEq, Repr

namespace RetransmitRequest

def encode (message : RetransmitRequest) : List UInt8 :=
  encodeUIntLE 8 message.uuid
    ++ encodeUIntLE 8 message.lastUuid
    ++ encodeUIntLE 8 message.requestTimestamp
    ++ encodeUIntLE 4 message.fromSeqNo
    ++ encodeUIntLE 2 message.msgCount16

def decode (bytes : List UInt8) : Option (RetransmitRequest × List UInt8) := do
  let (uuid, bytes) ← decodeUIntLE 8 bytes
  let (lastUuid, bytes) ← decodeUIntLE 8 bytes
  let (requestTimestamp, bytes) ← decodeUIntLE 8 bytes
  let (fromSeqNo, bytes) ← decodeUIntLE 4 bytes
  let (msgCount16, bytes) ← decodeUIntLE 2 bytes
  pure ({ uuid, lastUuid, requestTimestamp, fromSeqNo, msgCount16 }, bytes)

@[simp] theorem encode_length (message : RetransmitRequest) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : RetransmitRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetransmitRequest) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end RetransmitRequest

/-- New Order Single: 132 bytes -/
structure NewOrderSingle where
  priceOptional : BitVec 64
  orderQty : BitVec 32
  securityId : BitVec 32
  side : BitVec 8
  seqNum : BitVec 32
  senderId : Alpha 20
  clordid : Alpha 20
  partyDetailsListReqId : BitVec 64
  orderRequestId : BitVec 64
  sendingTimeEpoch : BitVec 64
  stopPx : BitVec 64
  location : Alpha 5
  minQty : BitVec 32
  displayQty : BitVec 32
  expireDate : BitVec 16
  ordType : OrdType
  timeInForce : BitVec 8
  manualOrderIndicator : BitVec 8
  execInst : BitVec 8
  executionMode : ExecutionMode
  liquidityFlag : BitVec 8
  managedOrder : BitVec 8
  shortSaleType : BitVec 8
  discretionPrice : BitVec 64
  reservationPrice : BitVec 64
  deriving DecidableEq, Repr

namespace NewOrderSingle

def encode (message : NewOrderSingle) : List UInt8 :=
  encodeUIntLE 8 message.priceOptional
    ++ encodeUIntLE 4 message.orderQty
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUInt 1 message.side
    ++ encodeUIntLE 4 message.seqNum
    ++ Alpha.encode message.senderId
    ++ Alpha.encode message.clordid
    ++ encodeUIntLE 8 message.partyDetailsListReqId
    ++ encodeUIntLE 8 message.orderRequestId
    ++ encodeUIntLE 8 message.sendingTimeEpoch
    ++ encodeUIntLE 8 message.stopPx
    ++ Alpha.encode message.location
    ++ encodeUIntLE 4 message.minQty
    ++ encodeUIntLE 4 message.displayQty
    ++ encodeUIntLE 2 message.expireDate
    ++ OrdType.encode message.ordType
    ++ encodeUInt 1 message.timeInForce
    ++ encodeUInt 1 message.manualOrderIndicator
    ++ encodeUIntLE 1 message.execInst
    ++ ExecutionMode.encode message.executionMode
    ++ encodeUInt 1 message.liquidityFlag
    ++ encodeUInt 1 message.managedOrder
    ++ encodeUInt 1 message.shortSaleType
    ++ encodeUIntLE 8 message.discretionPrice
    ++ encodeUIntLE 8 message.reservationPrice

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (NewOrderSingle × List UInt8) := do
  let (priceOptional, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (senderId, bytes) ← Alpha.decode 20 bytes
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (partyDetailsListReqId, bytes) ← decodeUIntLE 8 bytes
  let (orderRequestId, bytes) ← decodeUIntLE 8 bytes
  let (sendingTimeEpoch, bytes) ← decodeUIntLE 8 bytes
  let (stopPx, bytes) ← decodeUIntLE 8 bytes
  let (location, bytes) ← Alpha.decode 5 bytes
  let (minQty, bytes) ← decodeUIntLE 4 bytes
  let (displayQty, bytes) ← decodeUIntLE 4 bytes
  let (expireDate, bytes) ← decodeUIntLE 2 bytes
  let (ordType, bytes) ← OrdType.decode bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (manualOrderIndicator, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUIntLE 1 bytes
  let (executionMode, bytes) ← ExecutionMode.decode bytes
  let (liquidityFlag, bytes) ← decodeUInt 1 bytes
  let (managedOrder, bytes) ← decodeUInt 1 bytes
  let (shortSaleType, bytes) ← decodeUInt 1 bytes
  let (discretionPrice, bytes) ← decodeUIntLE 8 bytes
  let (reservationPrice, bytes) ← decodeUIntLE 8 bytes
  pure ({ priceOptional, orderQty, securityId, side, seqNum, senderId, clordid, partyDetailsListReqId, orderRequestId, sendingTimeEpoch, stopPx, location, minQty, displayQty, expireDate, ordType, timeInForce, manualOrderIndicator, execInst, executionMode, liquidityFlag, managedOrder, shortSaleType, discretionPrice, reservationPrice }, bytes)

@[simp] theorem encode_length (message : NewOrderSingle) : (encode message).length = 132 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, OrdType.encode_length, ExecutionMode.encode_length]

theorem encode_length_pos (message : NewOrderSingle) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewOrderSingle) (rest : List UInt8) :
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
  rw [OrdType.decode_encode]
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
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end NewOrderSingle

/-- Order Cancel Replace Request: 133 bytes -/
structure OrderCancelReplaceRequest where
  priceOptional : BitVec 64
  orderQty : BitVec 32
  securityId : BitVec 32
  side : BitVec 8
  seqNum : BitVec 32
  senderId : Alpha 20
  clordid : Alpha 20
  partyDetailsListReqId : BitVec 64
  orderIdOptional : BitVec 64
  stopPx : BitVec 64
  orderRequestId : BitVec 64
  sendingTimeEpoch : BitVec 64
  location : Alpha 5
  minQty : BitVec 32
  displayQty : BitVec 32
  expireDate : BitVec 16
  ordType : OrdType
  timeInForce : BitVec 8
  manualOrderIndicator : BitVec 8
  ofmOverride : BitVec 8
  execInst : BitVec 8
  executionMode : ExecutionMode
  liquidityFlag : BitVec 8
  managedOrder : BitVec 8
  shortSaleType : BitVec 8
  discretionPrice : BitVec 64
  deriving DecidableEq, Repr

namespace OrderCancelReplaceRequest

def encode (message : OrderCancelReplaceRequest) : List UInt8 :=
  encodeUIntLE 8 message.priceOptional
    ++ encodeUIntLE 4 message.orderQty
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUInt 1 message.side
    ++ encodeUIntLE 4 message.seqNum
    ++ Alpha.encode message.senderId
    ++ Alpha.encode message.clordid
    ++ encodeUIntLE 8 message.partyDetailsListReqId
    ++ encodeUIntLE 8 message.orderIdOptional
    ++ encodeUIntLE 8 message.stopPx
    ++ encodeUIntLE 8 message.orderRequestId
    ++ encodeUIntLE 8 message.sendingTimeEpoch
    ++ Alpha.encode message.location
    ++ encodeUIntLE 4 message.minQty
    ++ encodeUIntLE 4 message.displayQty
    ++ encodeUIntLE 2 message.expireDate
    ++ OrdType.encode message.ordType
    ++ encodeUInt 1 message.timeInForce
    ++ encodeUInt 1 message.manualOrderIndicator
    ++ encodeUInt 1 message.ofmOverride
    ++ encodeUIntLE 1 message.execInst
    ++ ExecutionMode.encode message.executionMode
    ++ encodeUInt 1 message.liquidityFlag
    ++ encodeUInt 1 message.managedOrder
    ++ encodeUInt 1 message.shortSaleType
    ++ encodeUIntLE 8 message.discretionPrice

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderCancelReplaceRequest × List UInt8) := do
  let (priceOptional, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (senderId, bytes) ← Alpha.decode 20 bytes
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (partyDetailsListReqId, bytes) ← decodeUIntLE 8 bytes
  let (orderIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (stopPx, bytes) ← decodeUIntLE 8 bytes
  let (orderRequestId, bytes) ← decodeUIntLE 8 bytes
  let (sendingTimeEpoch, bytes) ← decodeUIntLE 8 bytes
  let (location, bytes) ← Alpha.decode 5 bytes
  let (minQty, bytes) ← decodeUIntLE 4 bytes
  let (displayQty, bytes) ← decodeUIntLE 4 bytes
  let (expireDate, bytes) ← decodeUIntLE 2 bytes
  let (ordType, bytes) ← OrdType.decode bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (manualOrderIndicator, bytes) ← decodeUInt 1 bytes
  let (ofmOverride, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUIntLE 1 bytes
  let (executionMode, bytes) ← ExecutionMode.decode bytes
  let (liquidityFlag, bytes) ← decodeUInt 1 bytes
  let (managedOrder, bytes) ← decodeUInt 1 bytes
  let (shortSaleType, bytes) ← decodeUInt 1 bytes
  let (discretionPrice, bytes) ← decodeUIntLE 8 bytes
  pure ({ priceOptional, orderQty, securityId, side, seqNum, senderId, clordid, partyDetailsListReqId, orderIdOptional, stopPx, orderRequestId, sendingTimeEpoch, location, minQty, displayQty, expireDate, ordType, timeInForce, manualOrderIndicator, ofmOverride, execInst, executionMode, liquidityFlag, managedOrder, shortSaleType, discretionPrice }, bytes)

@[simp] theorem encode_length (message : OrderCancelReplaceRequest) : (encode message).length = 133 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, OrdType.encode_length, ExecutionMode.encode_length]

theorem encode_length_pos (message : OrderCancelReplaceRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancelReplaceRequest) (rest : List UInt8) :
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
  rw [OrdType.decode_encode]
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

end OrderCancelReplaceRequest

/-- Order Cancel Request: 96 bytes -/
structure OrderCancelRequest where
  orderIdOptional : BitVec 64
  partyDetailsListReqId : BitVec 64
  manualOrderIndicator : BitVec 8
  seqNum : BitVec 32
  senderId : Alpha 20
  clordid : Alpha 20
  orderRequestId : BitVec 64
  sendingTimeEpoch : BitVec 64
  location : Alpha 5
  securityId : BitVec 32
  side : BitVec 8
  liquidityFlag : BitVec 8
  origOrderUser : Alpha 8
  deriving DecidableEq, Repr

namespace OrderCancelRequest

def encode (message : OrderCancelRequest) : List UInt8 :=
  encodeUIntLE 8 message.orderIdOptional
    ++ encodeUIntLE 8 message.partyDetailsListReqId
    ++ encodeUInt 1 message.manualOrderIndicator
    ++ encodeUIntLE 4 message.seqNum
    ++ Alpha.encode message.senderId
    ++ Alpha.encode message.clordid
    ++ encodeUIntLE 8 message.orderRequestId
    ++ encodeUIntLE 8 message.sendingTimeEpoch
    ++ Alpha.encode message.location
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUInt 1 message.side
    ++ encodeUInt 1 message.liquidityFlag
    ++ Alpha.encode message.origOrderUser

def decode (bytes : List UInt8) : Option (OrderCancelRequest × List UInt8) := do
  let (orderIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (partyDetailsListReqId, bytes) ← decodeUIntLE 8 bytes
  let (manualOrderIndicator, bytes) ← decodeUInt 1 bytes
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (senderId, bytes) ← Alpha.decode 20 bytes
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (orderRequestId, bytes) ← decodeUIntLE 8 bytes
  let (sendingTimeEpoch, bytes) ← decodeUIntLE 8 bytes
  let (location, bytes) ← Alpha.decode 5 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (liquidityFlag, bytes) ← decodeUInt 1 bytes
  let (origOrderUser, bytes) ← Alpha.decode 8 bytes
  pure ({ orderIdOptional, partyDetailsListReqId, manualOrderIndicator, seqNum, senderId, clordid, orderRequestId, sendingTimeEpoch, location, securityId, side, liquidityFlag, origOrderUser }, bytes)

@[simp] theorem encode_length (message : OrderCancelRequest) : (encode message).length = 96 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderCancelRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancelRequest) (rest : List UInt8) :
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
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end OrderCancelRequest

/-- Quote Entries Group: 38 bytes -/
structure QuoteEntriesGroup where
  bidPx : BitVec 64
  offerPx : BitVec 64
  quoteEntryId : BitVec 32
  securityId : BitVec 32
  bidSize : BitVec 32
  offerSize : BitVec 32
  underlyingSecurityId : BitVec 32
  quoteSetId : BitVec 16
  deriving DecidableEq, Repr

namespace QuoteEntriesGroup

def encode (message : QuoteEntriesGroup) : List UInt8 :=
  encodeUIntLE 8 message.bidPx
    ++ encodeUIntLE 8 message.offerPx
    ++ encodeUIntLE 4 message.quoteEntryId
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 4 message.bidSize
    ++ encodeUIntLE 4 message.offerSize
    ++ encodeUIntLE 4 message.underlyingSecurityId
    ++ encodeUIntLE 2 message.quoteSetId

def decode (bytes : List UInt8) : Option (QuoteEntriesGroup × List UInt8) := do
  let (bidPx, bytes) ← decodeUIntLE 8 bytes
  let (offerPx, bytes) ← decodeUIntLE 8 bytes
  let (quoteEntryId, bytes) ← decodeUIntLE 4 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (bidSize, bytes) ← decodeUIntLE 4 bytes
  let (offerSize, bytes) ← decodeUIntLE 4 bytes
  let (underlyingSecurityId, bytes) ← decodeUIntLE 4 bytes
  let (quoteSetId, bytes) ← decodeUIntLE 2 bytes
  pure ({ bidPx, offerPx, quoteEntryId, securityId, bidSize, offerSize, underlyingSecurityId, quoteSetId }, bytes)

@[simp] theorem encode_length (message : QuoteEntriesGroup) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : QuoteEntriesGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteEntriesGroup) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end QuoteEntriesGroup

/-- Quote Entries Groups -/
structure QuoteEntriesGroups where
  blockLength : BitVec 16
  quoteEntriesGroup : Bounded 1 QuoteEntriesGroup
  deriving DecidableEq, Repr

namespace QuoteEntriesGroups

def encode (message : QuoteEntriesGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.quoteEntriesGroup.val.length)
    ++ encodeMany QuoteEntriesGroup.encode message.quoteEntriesGroup.val

def decode (bytes : List UInt8) : Option (QuoteEntriesGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (quoteEntriesGroup_, bytes) ← decodeMany QuoteEntriesGroup.decode numInGroup.toNat bytes
  if fits_quoteEntriesGroup : quoteEntriesGroup_.length < 256 ^ 1 then
    pure ({ blockLength, quoteEntriesGroup := ⟨quoteEntriesGroup_, fits_quoteEntriesGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : QuoteEntriesGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : QuoteEntriesGroups) : (encode message).length ≤ 9693 := by
  have bound_quoteEntriesGroup := message.quoteEntriesGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const QuoteEntriesGroup.encode 38 QuoteEntriesGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : QuoteEntriesGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 QuoteEntriesGroup.encode QuoteEntriesGroup.decode QuoteEntriesGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.quoteEntriesGroup.length_lt, ↓reduceDIte]
  rfl

end QuoteEntriesGroups

/-- Mass Quote -/
structure MassQuote where
  partyDetailsListReqId : BitVec 64
  sendingTimeEpoch : BitVec 64
  manualOrderIndicator : BitVec 8
  seqNum : BitVec 32
  senderId : Alpha 20
  quoteReqIdOptional : BitVec 64
  location : Alpha 5
  quoteId : BitVec 32
  totNoQuoteEntries : BitVec 8
  mmProtectionReset : BitVec 8
  liquidityFlag : BitVec 8
  shortSaleType : BitVec 8
  unused30 : Alpha 30
  future30 : Alpha 30
  quoteEntryOpen : BitVec 8
  quoteEntriesGroups : QuoteEntriesGroups
  deriving DecidableEq, Repr

namespace MassQuote

def encode (message : MassQuote) : List UInt8 :=
  encodeUIntLE 8 message.partyDetailsListReqId
    ++ encodeUIntLE 8 message.sendingTimeEpoch
    ++ encodeUInt 1 message.manualOrderIndicator
    ++ encodeUIntLE 4 message.seqNum
    ++ Alpha.encode message.senderId
    ++ encodeUIntLE 8 message.quoteReqIdOptional
    ++ Alpha.encode message.location
    ++ encodeUIntLE 4 message.quoteId
    ++ encodeUInt 1 message.totNoQuoteEntries
    ++ encodeUInt 1 message.mmProtectionReset
    ++ encodeUInt 1 message.liquidityFlag
    ++ encodeUInt 1 message.shortSaleType
    ++ Alpha.encode message.unused30
    ++ Alpha.encode message.future30
    ++ encodeUInt 1 message.quoteEntryOpen
    ++ QuoteEntriesGroups.encode message.quoteEntriesGroups

def decode (bytes : List UInt8) : Option (MassQuote × List UInt8) := do
  let (partyDetailsListReqId, bytes) ← decodeUIntLE 8 bytes
  let (sendingTimeEpoch, bytes) ← decodeUIntLE 8 bytes
  let (manualOrderIndicator, bytes) ← decodeUInt 1 bytes
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (senderId, bytes) ← Alpha.decode 20 bytes
  let (quoteReqIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (location, bytes) ← Alpha.decode 5 bytes
  let (quoteId, bytes) ← decodeUIntLE 4 bytes
  let (totNoQuoteEntries, bytes) ← decodeUInt 1 bytes
  let (mmProtectionReset, bytes) ← decodeUInt 1 bytes
  let (liquidityFlag, bytes) ← decodeUInt 1 bytes
  let (shortSaleType, bytes) ← decodeUInt 1 bytes
  let (unused30, bytes) ← Alpha.decode 30 bytes
  let (future30, bytes) ← Alpha.decode 30 bytes
  let (quoteEntryOpen, bytes) ← decodeUInt 1 bytes
  let (quoteEntriesGroups, bytes) ← QuoteEntriesGroups.decode bytes
  pure ({ partyDetailsListReqId, sendingTimeEpoch, manualOrderIndicator, seqNum, senderId, quoteReqIdOptional, location, quoteId, totNoQuoteEntries, mmProtectionReset, liquidityFlag, shortSaleType, unused30, future30, quoteEntryOpen, quoteEntriesGroups }, bytes)

theorem encode_length_pos (message : MassQuote) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MassQuote) : (encode message).length ≤ 9816 := by
  have bound_quoteEntriesGroups := QuoteEntriesGroups.encode_length_le message.quoteEntriesGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : MassQuote) (rest : List UInt8) :
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
  rw [Alpha.decode_encode]
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
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [QuoteEntriesGroups.decode_encode, Option.bind_some]
  rfl

end MassQuote

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

/-- Party Details Definition Request -/
structure PartyDetailsDefinitionRequest where
  partyDetailsListReqId : BitVec 64
  sendingTimeEpoch : BitVec 64
  listUpdateAction : ListUpdateAction
  seqNum : BitVec 32
  memo : Alpha 75
  avgPxGroupId : Alpha 20
  selfMatchPreventionId : BitVec 64
  cmtaGiveupCd : CmtaGiveupCd
  custOrderCapacity : BitVec 8
  clearingAccountType : BitVec 8
  selfMatchPreventionInstruction : SelfMatchPreventionInstruction
  avgPxIndicator : BitVec 8
  clearingTradePriceType : BitVec 8
  custOrderHandlingInst : CustOrderHandlingInst
  executor : BitVec 64
  idmShortCode : BitVec 64
  partyDetailsGroups : PartyDetailsGroups
  trdRegPublicationsGroups : TrdRegPublicationsGroups
  deriving DecidableEq, Repr

namespace PartyDetailsDefinitionRequest

def encode (message : PartyDetailsDefinitionRequest) : List UInt8 :=
  encodeUIntLE 8 message.partyDetailsListReqId
    ++ encodeUIntLE 8 message.sendingTimeEpoch
    ++ ListUpdateAction.encode message.listUpdateAction
    ++ encodeUIntLE 4 message.seqNum
    ++ Alpha.encode message.memo
    ++ Alpha.encode message.avgPxGroupId
    ++ encodeUIntLE 8 message.selfMatchPreventionId
    ++ CmtaGiveupCd.encode message.cmtaGiveupCd
    ++ encodeUInt 1 message.custOrderCapacity
    ++ encodeUInt 1 message.clearingAccountType
    ++ SelfMatchPreventionInstruction.encode message.selfMatchPreventionInstruction
    ++ encodeUInt 1 message.avgPxIndicator
    ++ encodeUInt 1 message.clearingTradePriceType
    ++ CustOrderHandlingInst.encode message.custOrderHandlingInst
    ++ encodeUIntLE 8 message.executor
    ++ encodeUIntLE 8 message.idmShortCode
    ++ PartyDetailsGroups.encode message.partyDetailsGroups
    ++ TrdRegPublicationsGroups.encode message.trdRegPublicationsGroups

def decode (bytes : List UInt8) : Option (PartyDetailsDefinitionRequest × List UInt8) := do
  let (partyDetailsListReqId, bytes) ← decodeUIntLE 8 bytes
  let (sendingTimeEpoch, bytes) ← decodeUIntLE 8 bytes
  let (listUpdateAction, bytes) ← ListUpdateAction.decode bytes
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (memo, bytes) ← Alpha.decode 75 bytes
  let (avgPxGroupId, bytes) ← Alpha.decode 20 bytes
  let (selfMatchPreventionId, bytes) ← decodeUIntLE 8 bytes
  let (cmtaGiveupCd, bytes) ← CmtaGiveupCd.decode bytes
  let (custOrderCapacity, bytes) ← decodeUInt 1 bytes
  let (clearingAccountType, bytes) ← decodeUInt 1 bytes
  let (selfMatchPreventionInstruction, bytes) ← SelfMatchPreventionInstruction.decode bytes
  let (avgPxIndicator, bytes) ← decodeUInt 1 bytes
  let (clearingTradePriceType, bytes) ← decodeUInt 1 bytes
  let (custOrderHandlingInst, bytes) ← CustOrderHandlingInst.decode bytes
  let (executor, bytes) ← decodeUIntLE 8 bytes
  let (idmShortCode, bytes) ← decodeUIntLE 8 bytes
  let (partyDetailsGroups, bytes) ← PartyDetailsGroups.decode bytes
  let (trdRegPublicationsGroups, bytes) ← TrdRegPublicationsGroups.decode bytes
  pure ({ partyDetailsListReqId, sendingTimeEpoch, listUpdateAction, seqNum, memo, avgPxGroupId, selfMatchPreventionId, cmtaGiveupCd, custOrderCapacity, clearingAccountType, selfMatchPreventionInstruction, avgPxIndicator, clearingTradePriceType, custOrderHandlingInst, executor, idmShortCode, partyDetailsGroups, trdRegPublicationsGroups }, bytes)

theorem encode_length_pos (message : PartyDetailsDefinitionRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : PartyDetailsDefinitionRequest) : (encode message).length ≤ 6273 := by
  have bound_partyDetailsGroups := PartyDetailsGroups.encode_length_le message.partyDetailsGroups
  have bound_trdRegPublicationsGroups := TrdRegPublicationsGroups.encode_length_le message.trdRegPublicationsGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, ListUpdateAction.encode_length, Alpha.encode_length, CmtaGiveupCd.encode_length, encodeUInt_length, SelfMatchPreventionInstruction.encode_length, CustOrderHandlingInst.encode_length]
  omega

@[simp] theorem decode_encode (message : PartyDetailsDefinitionRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [ListUpdateAction.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [CmtaGiveupCd.decode_encode]
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
  rw [CustOrderHandlingInst.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [PartyDetailsGroups.decode_encode]
  simp only [Option.bind_some]
  rw [TrdRegPublicationsGroups.decode_encode, Option.bind_some]
  rfl

end PartyDetailsDefinitionRequest

/-- Quote Cancel Entries Group: 10 bytes -/
structure QuoteCancelEntriesGroup where
  securityGroup : Alpha 6
  securityIdOptional : BitVec 32
  deriving DecidableEq, Repr

namespace QuoteCancelEntriesGroup

def encode (message : QuoteCancelEntriesGroup) : List UInt8 :=
  Alpha.encode message.securityGroup
    ++ encodeUIntLE 4 message.securityIdOptional

def decode (bytes : List UInt8) : Option (QuoteCancelEntriesGroup × List UInt8) := do
  let (securityGroup, bytes) ← Alpha.decode 6 bytes
  let (securityIdOptional, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityGroup, securityIdOptional }, bytes)

@[simp] theorem encode_length (message : QuoteCancelEntriesGroup) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : QuoteCancelEntriesGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteCancelEntriesGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end QuoteCancelEntriesGroup

/-- Quote Cancel Entries Groups -/
structure QuoteCancelEntriesGroups where
  blockLength : BitVec 16
  quoteCancelEntriesGroup : Bounded 1 QuoteCancelEntriesGroup
  deriving DecidableEq, Repr

namespace QuoteCancelEntriesGroups

def encode (message : QuoteCancelEntriesGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.quoteCancelEntriesGroup.val.length)
    ++ encodeMany QuoteCancelEntriesGroup.encode message.quoteCancelEntriesGroup.val

def decode (bytes : List UInt8) : Option (QuoteCancelEntriesGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (quoteCancelEntriesGroup_, bytes) ← decodeMany QuoteCancelEntriesGroup.decode numInGroup.toNat bytes
  if fits_quoteCancelEntriesGroup : quoteCancelEntriesGroup_.length < 256 ^ 1 then
    pure ({ blockLength, quoteCancelEntriesGroup := ⟨quoteCancelEntriesGroup_, fits_quoteCancelEntriesGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : QuoteCancelEntriesGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : QuoteCancelEntriesGroups) : (encode message).length ≤ 2553 := by
  have bound_quoteCancelEntriesGroup := message.quoteCancelEntriesGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const QuoteCancelEntriesGroup.encode 10 QuoteCancelEntriesGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : QuoteCancelEntriesGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 QuoteCancelEntriesGroup.encode QuoteCancelEntriesGroup.decode QuoteCancelEntriesGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.quoteCancelEntriesGroup.length_lt, ↓reduceDIte]
  rfl

end QuoteCancelEntriesGroups

/-- Quote Cancel Sets Group: 10 bytes -/
structure QuoteCancelSetsGroup where
  bidSize : BitVec 32
  offerSize : BitVec 32
  quoteSetId : BitVec 16
  deriving DecidableEq, Repr

namespace QuoteCancelSetsGroup

def encode (message : QuoteCancelSetsGroup) : List UInt8 :=
  encodeUIntLE 4 message.bidSize
    ++ encodeUIntLE 4 message.offerSize
    ++ encodeUIntLE 2 message.quoteSetId

def decode (bytes : List UInt8) : Option (QuoteCancelSetsGroup × List UInt8) := do
  let (bidSize, bytes) ← decodeUIntLE 4 bytes
  let (offerSize, bytes) ← decodeUIntLE 4 bytes
  let (quoteSetId, bytes) ← decodeUIntLE 2 bytes
  pure ({ bidSize, offerSize, quoteSetId }, bytes)

@[simp] theorem encode_length (message : QuoteCancelSetsGroup) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : QuoteCancelSetsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteCancelSetsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end QuoteCancelSetsGroup

/-- Quote Cancel Sets Groups -/
structure QuoteCancelSetsGroups where
  blockLength : BitVec 16
  quoteCancelSetsGroup : Bounded 1 QuoteCancelSetsGroup
  deriving DecidableEq, Repr

namespace QuoteCancelSetsGroups

def encode (message : QuoteCancelSetsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.quoteCancelSetsGroup.val.length)
    ++ encodeMany QuoteCancelSetsGroup.encode message.quoteCancelSetsGroup.val

def decode (bytes : List UInt8) : Option (QuoteCancelSetsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (quoteCancelSetsGroup_, bytes) ← decodeMany QuoteCancelSetsGroup.decode numInGroup.toNat bytes
  if fits_quoteCancelSetsGroup : quoteCancelSetsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, quoteCancelSetsGroup := ⟨quoteCancelSetsGroup_, fits_quoteCancelSetsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : QuoteCancelSetsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : QuoteCancelSetsGroups) : (encode message).length ≤ 2553 := by
  have bound_quoteCancelSetsGroup := message.quoteCancelSetsGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const QuoteCancelSetsGroup.encode 10 QuoteCancelSetsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : QuoteCancelSetsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 QuoteCancelSetsGroup.encode QuoteCancelSetsGroup.decode QuoteCancelSetsGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.quoteCancelSetsGroup.length_lt, ↓reduceDIte]
  rfl

end QuoteCancelSetsGroups

/-- Quote Cancel -/
structure QuoteCancel where
  partyDetailsListReqId : BitVec 64
  sendingTimeEpoch : BitVec 64
  manualOrderIndicator : BitVec 8
  seqNum : BitVec 32
  senderId : Alpha 20
  location : Alpha 5
  quoteId : BitVec 32
  quoteCancelType : BitVec 8
  liquidityFlag : BitVec 8
  origOrderUser : Alpha 8
  quoteEntryOpen : BitVec 8
  quoteCancelEntriesGroups : QuoteCancelEntriesGroups
  quoteCancelSetsGroups : QuoteCancelSetsGroups
  deriving DecidableEq, Repr

namespace QuoteCancel

def encode (message : QuoteCancel) : List UInt8 :=
  encodeUIntLE 8 message.partyDetailsListReqId
    ++ encodeUIntLE 8 message.sendingTimeEpoch
    ++ encodeUInt 1 message.manualOrderIndicator
    ++ encodeUIntLE 4 message.seqNum
    ++ Alpha.encode message.senderId
    ++ Alpha.encode message.location
    ++ encodeUIntLE 4 message.quoteId
    ++ encodeUInt 1 message.quoteCancelType
    ++ encodeUInt 1 message.liquidityFlag
    ++ Alpha.encode message.origOrderUser
    ++ encodeUInt 1 message.quoteEntryOpen
    ++ QuoteCancelEntriesGroups.encode message.quoteCancelEntriesGroups
    ++ QuoteCancelSetsGroups.encode message.quoteCancelSetsGroups

def decode (bytes : List UInt8) : Option (QuoteCancel × List UInt8) := do
  let (partyDetailsListReqId, bytes) ← decodeUIntLE 8 bytes
  let (sendingTimeEpoch, bytes) ← decodeUIntLE 8 bytes
  let (manualOrderIndicator, bytes) ← decodeUInt 1 bytes
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (senderId, bytes) ← Alpha.decode 20 bytes
  let (location, bytes) ← Alpha.decode 5 bytes
  let (quoteId, bytes) ← decodeUIntLE 4 bytes
  let (quoteCancelType, bytes) ← decodeUInt 1 bytes
  let (liquidityFlag, bytes) ← decodeUInt 1 bytes
  let (origOrderUser, bytes) ← Alpha.decode 8 bytes
  let (quoteEntryOpen, bytes) ← decodeUInt 1 bytes
  let (quoteCancelEntriesGroups, bytes) ← QuoteCancelEntriesGroups.decode bytes
  let (quoteCancelSetsGroups, bytes) ← QuoteCancelSetsGroups.decode bytes
  pure ({ partyDetailsListReqId, sendingTimeEpoch, manualOrderIndicator, seqNum, senderId, location, quoteId, quoteCancelType, liquidityFlag, origOrderUser, quoteEntryOpen, quoteCancelEntriesGroups, quoteCancelSetsGroups }, bytes)

theorem encode_length_pos (message : QuoteCancel) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : QuoteCancel) : (encode message).length ≤ 5167 := by
  have bound_quoteCancelEntriesGroups := QuoteCancelEntriesGroups.encode_length_le message.quoteCancelEntriesGroups
  have bound_quoteCancelSetsGroups := QuoteCancelSetsGroups.encode_length_le message.quoteCancelSetsGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : QuoteCancel) (rest : List UInt8) :
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
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [QuoteCancelEntriesGroups.decode_encode]
  simp only [Option.bind_some]
  rw [QuoteCancelSetsGroups.decode_encode, Option.bind_some]
  rfl

end QuoteCancel

/-- Order Mass Action Request: 79 bytes -/
structure OrderMassActionRequest where
  partyDetailsListReqId : BitVec 64
  orderRequestId : BitVec 64
  manualOrderIndicator : BitVec 8
  seqNum : BitVec 32
  senderId : Alpha 20
  sendingTimeEpoch : BitVec 64
  securityGroup : Alpha 6
  location : Alpha 5
  securityIdOptional : BitVec 32
  massActionScope : BitVec 8
  marketSegmentId : BitVec 8
  massCancelRequestType : BitVec 8
  sideOptional : BitVec 8
  massActionOrdTyp : MassActionOrdTyp
  massCancelTif : BitVec 8
  liquidityFlag : BitVec 8
  origOrderUser : Alpha 8
  deriving DecidableEq, Repr

namespace OrderMassActionRequest

def encode (message : OrderMassActionRequest) : List UInt8 :=
  encodeUIntLE 8 message.partyDetailsListReqId
    ++ encodeUIntLE 8 message.orderRequestId
    ++ encodeUInt 1 message.manualOrderIndicator
    ++ encodeUIntLE 4 message.seqNum
    ++ Alpha.encode message.senderId
    ++ encodeUIntLE 8 message.sendingTimeEpoch
    ++ Alpha.encode message.securityGroup
    ++ Alpha.encode message.location
    ++ encodeUIntLE 4 message.securityIdOptional
    ++ encodeUInt 1 message.massActionScope
    ++ encodeUInt 1 message.marketSegmentId
    ++ encodeUInt 1 message.massCancelRequestType
    ++ encodeUInt 1 message.sideOptional
    ++ MassActionOrdTyp.encode message.massActionOrdTyp
    ++ encodeUInt 1 message.massCancelTif
    ++ encodeUInt 1 message.liquidityFlag
    ++ Alpha.encode message.origOrderUser

def decode (bytes : List UInt8) : Option (OrderMassActionRequest × List UInt8) := do
  let (partyDetailsListReqId, bytes) ← decodeUIntLE 8 bytes
  let (orderRequestId, bytes) ← decodeUIntLE 8 bytes
  let (manualOrderIndicator, bytes) ← decodeUInt 1 bytes
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (senderId, bytes) ← Alpha.decode 20 bytes
  let (sendingTimeEpoch, bytes) ← decodeUIntLE 8 bytes
  let (securityGroup, bytes) ← Alpha.decode 6 bytes
  let (location, bytes) ← Alpha.decode 5 bytes
  let (securityIdOptional, bytes) ← decodeUIntLE 4 bytes
  let (massActionScope, bytes) ← decodeUInt 1 bytes
  let (marketSegmentId, bytes) ← decodeUInt 1 bytes
  let (massCancelRequestType, bytes) ← decodeUInt 1 bytes
  let (sideOptional, bytes) ← decodeUInt 1 bytes
  let (massActionOrdTyp, bytes) ← MassActionOrdTyp.decode bytes
  let (massCancelTif, bytes) ← decodeUInt 1 bytes
  let (liquidityFlag, bytes) ← decodeUInt 1 bytes
  let (origOrderUser, bytes) ← Alpha.decode 8 bytes
  pure ({ partyDetailsListReqId, orderRequestId, manualOrderIndicator, seqNum, senderId, sendingTimeEpoch, securityGroup, location, securityIdOptional, massActionScope, marketSegmentId, massCancelRequestType, sideOptional, massActionOrdTyp, massCancelTif, liquidityFlag, origOrderUser }, bytes)

@[simp] theorem encode_length (message : OrderMassActionRequest) : (encode message).length = 79 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, MassActionOrdTyp.encode_length]

theorem encode_length_pos (message : OrderMassActionRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderMassActionRequest) (rest : List UInt8) :
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
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
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
  rw [MassActionOrdTyp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end OrderMassActionRequest

/-- Order Mass Status Request: 68 bytes -/
structure OrderMassStatusRequest where
  partyDetailsListReqId : BitVec 64
  massStatusReqId : BitVec 64
  manualOrderIndicator : BitVec 8
  seqNum : BitVec 32
  senderId : Alpha 20
  sendingTimeEpoch : BitVec 64
  securityGroup : Alpha 6
  location : Alpha 5
  securityIdOptional : BitVec 32
  massStatusReqType : BitVec 8
  ordStatusReqType : BitVec 8
  massStatusTif : BitVec 8
  marketSegmentId : BitVec 8
  deriving DecidableEq, Repr

namespace OrderMassStatusRequest

def encode (message : OrderMassStatusRequest) : List UInt8 :=
  encodeUIntLE 8 message.partyDetailsListReqId
    ++ encodeUIntLE 8 message.massStatusReqId
    ++ encodeUInt 1 message.manualOrderIndicator
    ++ encodeUIntLE 4 message.seqNum
    ++ Alpha.encode message.senderId
    ++ encodeUIntLE 8 message.sendingTimeEpoch
    ++ Alpha.encode message.securityGroup
    ++ Alpha.encode message.location
    ++ encodeUIntLE 4 message.securityIdOptional
    ++ encodeUInt 1 message.massStatusReqType
    ++ encodeUInt 1 message.ordStatusReqType
    ++ encodeUInt 1 message.massStatusTif
    ++ encodeUInt 1 message.marketSegmentId

def decode (bytes : List UInt8) : Option (OrderMassStatusRequest × List UInt8) := do
  let (partyDetailsListReqId, bytes) ← decodeUIntLE 8 bytes
  let (massStatusReqId, bytes) ← decodeUIntLE 8 bytes
  let (manualOrderIndicator, bytes) ← decodeUInt 1 bytes
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (senderId, bytes) ← Alpha.decode 20 bytes
  let (sendingTimeEpoch, bytes) ← decodeUIntLE 8 bytes
  let (securityGroup, bytes) ← Alpha.decode 6 bytes
  let (location, bytes) ← Alpha.decode 5 bytes
  let (securityIdOptional, bytes) ← decodeUIntLE 4 bytes
  let (massStatusReqType, bytes) ← decodeUInt 1 bytes
  let (ordStatusReqType, bytes) ← decodeUInt 1 bytes
  let (massStatusTif, bytes) ← decodeUInt 1 bytes
  let (marketSegmentId, bytes) ← decodeUInt 1 bytes
  pure ({ partyDetailsListReqId, massStatusReqId, manualOrderIndicator, seqNum, senderId, sendingTimeEpoch, securityGroup, location, securityIdOptional, massStatusReqType, ordStatusReqType, massStatusTif, marketSegmentId }, bytes)

@[simp] theorem encode_length (message : OrderMassStatusRequest) : (encode message).length = 68 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderMassStatusRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderMassStatusRequest) (rest : List UInt8) :
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
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end OrderMassStatusRequest

/-- Order Status Request: 62 bytes -/
structure OrderStatusRequest where
  partyDetailsListReqId : BitVec 64
  ordStatusReqId : BitVec 64
  manualOrderIndicator : BitVec 8
  seqNum : BitVec 32
  senderId : Alpha 20
  orderId : BitVec 64
  sendingTimeEpoch : BitVec 64
  location : Alpha 5
  deriving DecidableEq, Repr

namespace OrderStatusRequest

def encode (message : OrderStatusRequest) : List UInt8 :=
  encodeUIntLE 8 message.partyDetailsListReqId
    ++ encodeUIntLE 8 message.ordStatusReqId
    ++ encodeUInt 1 message.manualOrderIndicator
    ++ encodeUIntLE 4 message.seqNum
    ++ Alpha.encode message.senderId
    ++ encodeUIntLE 8 message.orderId
    ++ encodeUIntLE 8 message.sendingTimeEpoch
    ++ Alpha.encode message.location

def decode (bytes : List UInt8) : Option (OrderStatusRequest × List UInt8) := do
  let (partyDetailsListReqId, bytes) ← decodeUIntLE 8 bytes
  let (ordStatusReqId, bytes) ← decodeUIntLE 8 bytes
  let (manualOrderIndicator, bytes) ← decodeUInt 1 bytes
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (senderId, bytes) ← Alpha.decode 20 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (sendingTimeEpoch, bytes) ← decodeUIntLE 8 bytes
  let (location, bytes) ← Alpha.decode 5 bytes
  pure ({ partyDetailsListReqId, ordStatusReqId, manualOrderIndicator, seqNum, senderId, orderId, sendingTimeEpoch, location }, bytes)

@[simp] theorem encode_length (message : OrderStatusRequest) : (encode message).length = 62 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderStatusRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderStatusRequest) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end OrderStatusRequest

/-- Requesting Party Ids Group: 7 bytes -/
structure RequestingPartyIdsGroup where
  requestingPartyId : Alpha 5
  requestingPartyIdSource : Alpha 1
  requestingPartyRole : Alpha 1
  deriving DecidableEq, Repr

namespace RequestingPartyIdsGroup

def encode (message : RequestingPartyIdsGroup) : List UInt8 :=
  Alpha.encode message.requestingPartyId
    ++ Alpha.encode message.requestingPartyIdSource
    ++ Alpha.encode message.requestingPartyRole

def decode (bytes : List UInt8) : Option (RequestingPartyIdsGroup × List UInt8) := do
  let (requestingPartyId, bytes) ← Alpha.decode 5 bytes
  let (requestingPartyIdSource, bytes) ← Alpha.decode 1 bytes
  let (requestingPartyRole, bytes) ← Alpha.decode 1 bytes
  pure ({ requestingPartyId, requestingPartyIdSource, requestingPartyRole }, bytes)

@[simp] theorem encode_length (message : RequestingPartyIdsGroup) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : RequestingPartyIdsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RequestingPartyIdsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end RequestingPartyIdsGroup

/-- Requesting Party Ids Groups -/
structure RequestingPartyIdsGroups where
  blockLength : BitVec 16
  requestingPartyIdsGroup : Bounded 1 RequestingPartyIdsGroup
  deriving DecidableEq, Repr

namespace RequestingPartyIdsGroups

def encode (message : RequestingPartyIdsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.requestingPartyIdsGroup.val.length)
    ++ encodeMany RequestingPartyIdsGroup.encode message.requestingPartyIdsGroup.val

def decode (bytes : List UInt8) : Option (RequestingPartyIdsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (requestingPartyIdsGroup_, bytes) ← decodeMany RequestingPartyIdsGroup.decode numInGroup.toNat bytes
  if fits_requestingPartyIdsGroup : requestingPartyIdsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, requestingPartyIdsGroup := ⟨requestingPartyIdsGroup_, fits_requestingPartyIdsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : RequestingPartyIdsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : RequestingPartyIdsGroups) : (encode message).length ≤ 1788 := by
  have bound_requestingPartyIdsGroup := message.requestingPartyIdsGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const RequestingPartyIdsGroup.encode 7 RequestingPartyIdsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : RequestingPartyIdsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 RequestingPartyIdsGroup.encode RequestingPartyIdsGroup.decode RequestingPartyIdsGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.requestingPartyIdsGroup.length_lt, ↓reduceDIte]
  rfl

end RequestingPartyIdsGroups

/-- Party Ids Group: 11 bytes -/
structure PartyIdsGroup where
  partyId : BitVec 64
  partyIdSource : Alpha 1
  partyRole : BitVec 16
  deriving DecidableEq, Repr

namespace PartyIdsGroup

def encode (message : PartyIdsGroup) : List UInt8 :=
  encodeUIntLE 8 message.partyId
    ++ Alpha.encode message.partyIdSource
    ++ encodeUIntLE 2 message.partyRole

def decode (bytes : List UInt8) : Option (PartyIdsGroup × List UInt8) := do
  let (partyId, bytes) ← decodeUIntLE 8 bytes
  let (partyIdSource, bytes) ← Alpha.decode 1 bytes
  let (partyRole, bytes) ← decodeUIntLE 2 bytes
  pure ({ partyId, partyIdSource, partyRole }, bytes)

@[simp] theorem encode_length (message : PartyIdsGroup) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : PartyIdsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PartyIdsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end PartyIdsGroup

/-- Party Ids Groups -/
structure PartyIdsGroups where
  blockLength : BitVec 16
  partyIdsGroup : Bounded 1 PartyIdsGroup
  deriving DecidableEq, Repr

namespace PartyIdsGroups

def encode (message : PartyIdsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.partyIdsGroup.val.length)
    ++ encodeMany PartyIdsGroup.encode message.partyIdsGroup.val

def decode (bytes : List UInt8) : Option (PartyIdsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (partyIdsGroup_, bytes) ← decodeMany PartyIdsGroup.decode numInGroup.toNat bytes
  if fits_partyIdsGroup : partyIdsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, partyIdsGroup := ⟨partyIdsGroup_, fits_partyIdsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : PartyIdsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : PartyIdsGroups) : (encode message).length ≤ 2808 := by
  have bound_partyIdsGroup := message.partyIdsGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const PartyIdsGroup.encode 11 PartyIdsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : PartyIdsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 PartyIdsGroup.encode PartyIdsGroup.decode PartyIdsGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.partyIdsGroup.length_lt, ↓reduceDIte]
  rfl

end PartyIdsGroups

/-- Party Details List Request -/
structure PartyDetailsListRequest where
  partyDetailsListReqId : BitVec 64
  sendingTimeEpoch : BitVec 64
  seqNum : BitVec 32
  requestingPartyIdsGroups : RequestingPartyIdsGroups
  partyIdsGroups : PartyIdsGroups
  deriving DecidableEq, Repr

namespace PartyDetailsListRequest

def encode (message : PartyDetailsListRequest) : List UInt8 :=
  encodeUIntLE 8 message.partyDetailsListReqId
    ++ encodeUIntLE 8 message.sendingTimeEpoch
    ++ encodeUIntLE 4 message.seqNum
    ++ RequestingPartyIdsGroups.encode message.requestingPartyIdsGroups
    ++ PartyIdsGroups.encode message.partyIdsGroups

def decode (bytes : List UInt8) : Option (PartyDetailsListRequest × List UInt8) := do
  let (partyDetailsListReqId, bytes) ← decodeUIntLE 8 bytes
  let (sendingTimeEpoch, bytes) ← decodeUIntLE 8 bytes
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (requestingPartyIdsGroups, bytes) ← RequestingPartyIdsGroups.decode bytes
  let (partyIdsGroups, bytes) ← PartyIdsGroups.decode bytes
  pure ({ partyDetailsListReqId, sendingTimeEpoch, seqNum, requestingPartyIdsGroups, partyIdsGroups }, bytes)

theorem encode_length_pos (message : PartyDetailsListRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : PartyDetailsListRequest) : (encode message).length ≤ 4616 := by
  have bound_requestingPartyIdsGroups := RequestingPartyIdsGroups.encode_length_le message.requestingPartyIdsGroups
  have bound_partyIdsGroups := PartyIdsGroups.encode_length_le message.partyIdsGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]
  omega

@[simp] theorem decode_encode (message : PartyDetailsListRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [RequestingPartyIdsGroups.decode_encode]
  simp only [Option.bind_some]
  rw [PartyIdsGroups.decode_encode, Option.bind_some]
  rfl

end PartyDetailsListRequest

/-- Related Sym Group: 9 bytes -/
structure RelatedSymGroup where
  securityId : BitVec 32
  orderQtyOptional : BitVec 32
  rfqSide : BitVec 8
  deriving DecidableEq, Repr

namespace RelatedSymGroup

def encode (message : RelatedSymGroup) : List UInt8 :=
  encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 4 message.orderQtyOptional
    ++ encodeUInt 1 message.rfqSide

def decode (bytes : List UInt8) : Option (RelatedSymGroup × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (orderQtyOptional, bytes) ← decodeUIntLE 4 bytes
  let (rfqSide, bytes) ← decodeUInt 1 bytes
  pure ({ securityId, orderQtyOptional, rfqSide }, bytes)

@[simp] theorem encode_length (message : RelatedSymGroup) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : RelatedSymGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RelatedSymGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end RelatedSymGroup

/-- Related Sym Groups -/
structure RelatedSymGroups where
  blockLength : BitVec 16
  relatedSymGroup : Bounded 1 RelatedSymGroup
  deriving DecidableEq, Repr

namespace RelatedSymGroups

def encode (message : RelatedSymGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.relatedSymGroup.val.length)
    ++ encodeMany RelatedSymGroup.encode message.relatedSymGroup.val

def decode (bytes : List UInt8) : Option (RelatedSymGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (relatedSymGroup_, bytes) ← decodeMany RelatedSymGroup.decode numInGroup.toNat bytes
  if fits_relatedSymGroup : relatedSymGroup_.length < 256 ^ 1 then
    pure ({ blockLength, relatedSymGroup := ⟨relatedSymGroup_, fits_relatedSymGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : RelatedSymGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : RelatedSymGroups) : (encode message).length ≤ 2298 := by
  have bound_relatedSymGroup := message.relatedSymGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const RelatedSymGroup.encode 9 RelatedSymGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : RelatedSymGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 RelatedSymGroup.encode RelatedSymGroup.decode RelatedSymGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.relatedSymGroup.length_lt, ↓reduceDIte]
  rfl

end RelatedSymGroups

/-- Request For Quote -/
structure RequestForQuote where
  partyDetailsListReqId : BitVec 64
  quoteReqId : BitVec 64
  manualOrderIndicator : BitVec 8
  seqNum : BitVec 32
  senderId : Alpha 20
  sendingTimeEpoch : BitVec 64
  location : Alpha 5
  quoteType : BitVec 8
  relatedSymGroups : RelatedSymGroups
  deriving DecidableEq, Repr

namespace RequestForQuote

def encode (message : RequestForQuote) : List UInt8 :=
  encodeUIntLE 8 message.partyDetailsListReqId
    ++ encodeUIntLE 8 message.quoteReqId
    ++ encodeUInt 1 message.manualOrderIndicator
    ++ encodeUIntLE 4 message.seqNum
    ++ Alpha.encode message.senderId
    ++ encodeUIntLE 8 message.sendingTimeEpoch
    ++ Alpha.encode message.location
    ++ encodeUInt 1 message.quoteType
    ++ RelatedSymGroups.encode message.relatedSymGroups

def decode (bytes : List UInt8) : Option (RequestForQuote × List UInt8) := do
  let (partyDetailsListReqId, bytes) ← decodeUIntLE 8 bytes
  let (quoteReqId, bytes) ← decodeUIntLE 8 bytes
  let (manualOrderIndicator, bytes) ← decodeUInt 1 bytes
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (senderId, bytes) ← Alpha.decode 20 bytes
  let (sendingTimeEpoch, bytes) ← decodeUIntLE 8 bytes
  let (location, bytes) ← Alpha.decode 5 bytes
  let (quoteType, bytes) ← decodeUInt 1 bytes
  let (relatedSymGroups, bytes) ← RelatedSymGroups.decode bytes
  pure ({ partyDetailsListReqId, quoteReqId, manualOrderIndicator, seqNum, senderId, sendingTimeEpoch, location, quoteType, relatedSymGroups }, bytes)

theorem encode_length_pos (message : RequestForQuote) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : RequestForQuote) : (encode message).length ≤ 2353 := by
  have bound_relatedSymGroups := RelatedSymGroups.encode_length_le message.relatedSymGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : RequestForQuote) (rest : List UInt8) :
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
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [RelatedSymGroups.decode_encode, Option.bind_some]
  rfl

end RequestForQuote

/-- Sides Group: 34 bytes -/
structure SidesGroup where
  clordid : Alpha 20
  partyDetailsListReqId : BitVec 64
  orderQty : BitVec 32
  side : BitVec 8
  sideTimeInForce : BitVec 8
  deriving DecidableEq, Repr

namespace SidesGroup

def encode (message : SidesGroup) : List UInt8 :=
  Alpha.encode message.clordid
    ++ encodeUIntLE 8 message.partyDetailsListReqId
    ++ encodeUIntLE 4 message.orderQty
    ++ encodeUInt 1 message.side
    ++ encodeUInt 1 message.sideTimeInForce

def decode (bytes : List UInt8) : Option (SidesGroup × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (partyDetailsListReqId, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (sideTimeInForce, bytes) ← decodeUInt 1 bytes
  pure ({ clordid, partyDetailsListReqId, orderQty, side, sideTimeInForce }, bytes)

@[simp] theorem encode_length (message : SidesGroup) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : SidesGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SidesGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
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

end SidesGroup

/-- Sides Groups -/
structure SidesGroups where
  blockLength : BitVec 16
  sidesGroup : Bounded 1 SidesGroup
  deriving DecidableEq, Repr

namespace SidesGroups

def encode (message : SidesGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.sidesGroup.val.length)
    ++ encodeMany SidesGroup.encode message.sidesGroup.val

def decode (bytes : List UInt8) : Option (SidesGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (sidesGroup_, bytes) ← decodeMany SidesGroup.decode numInGroup.toNat bytes
  if fits_sidesGroup : sidesGroup_.length < 256 ^ 1 then
    pure ({ blockLength, sidesGroup := ⟨sidesGroup_, fits_sidesGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : SidesGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SidesGroups) : (encode message).length ≤ 8673 := by
  have bound_sidesGroup := message.sidesGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const SidesGroup.encode 34 SidesGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : SidesGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 SidesGroup.encode SidesGroup.decode SidesGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.sidesGroup.length_lt, ↓reduceDIte]
  rfl

end SidesGroups

/-- New Order Cross -/
structure NewOrderCross where
  crossId : BitVec 64
  orderRequestId : BitVec 64
  manualOrderIndicator : BitVec 8
  seqNum : BitVec 32
  senderId : Alpha 20
  price : BitVec 64
  transBkdTime : BitVec 64
  sendingTimeEpoch : BitVec 64
  location : Alpha 5
  securityId : BitVec 32
  sidesGroups : SidesGroups
  deriving DecidableEq, Repr

namespace NewOrderCross

def encode (message : NewOrderCross) : List UInt8 :=
  encodeUIntLE 8 message.crossId
    ++ encodeUIntLE 8 message.orderRequestId
    ++ encodeUInt 1 message.manualOrderIndicator
    ++ encodeUIntLE 4 message.seqNum
    ++ Alpha.encode message.senderId
    ++ encodeUIntLE 8 message.price
    ++ encodeUIntLE 8 message.transBkdTime
    ++ encodeUIntLE 8 message.sendingTimeEpoch
    ++ Alpha.encode message.location
    ++ encodeUIntLE 4 message.securityId
    ++ SidesGroups.encode message.sidesGroups

def decode (bytes : List UInt8) : Option (NewOrderCross × List UInt8) := do
  let (crossId, bytes) ← decodeUIntLE 8 bytes
  let (orderRequestId, bytes) ← decodeUIntLE 8 bytes
  let (manualOrderIndicator, bytes) ← decodeUInt 1 bytes
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (senderId, bytes) ← Alpha.decode 20 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (transBkdTime, bytes) ← decodeUIntLE 8 bytes
  let (sendingTimeEpoch, bytes) ← decodeUIntLE 8 bytes
  let (location, bytes) ← Alpha.decode 5 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (sidesGroups, bytes) ← SidesGroups.decode bytes
  pure ({ crossId, orderRequestId, manualOrderIndicator, seqNum, senderId, price, transBkdTime, sendingTimeEpoch, location, securityId, sidesGroups }, bytes)

theorem encode_length_pos (message : NewOrderCross) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : NewOrderCross) : (encode message).length ≤ 8747 := by
  have bound_sidesGroups := SidesGroups.encode_length_le message.sidesGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : NewOrderCross) (rest : List UInt8) :
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
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [SidesGroups.decode_encode, Option.bind_some]
  rfl

end NewOrderCross

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

/-- Request Legs Group: 19 bytes -/
structure RequestLegsGroup where
  legPrice : BitVec 64
  legSecurityId : BitVec 32
  legOptionDelta : LegOptionDelta
  legSide : BitVec 8
  legRatioQty : BitVec 8
  deriving DecidableEq, Repr

namespace RequestLegsGroup

def encode (message : RequestLegsGroup) : List UInt8 :=
  encodeUIntLE 8 message.legPrice
    ++ encodeUIntLE 4 message.legSecurityId
    ++ LegOptionDelta.encode message.legOptionDelta
    ++ encodeUInt 1 message.legSide
    ++ encodeUInt 1 message.legRatioQty

def decode (bytes : List UInt8) : Option (RequestLegsGroup × List UInt8) := do
  let (legPrice, bytes) ← decodeUIntLE 8 bytes
  let (legSecurityId, bytes) ← decodeUIntLE 4 bytes
  let (legOptionDelta, bytes) ← LegOptionDelta.decode bytes
  let (legSide, bytes) ← decodeUInt 1 bytes
  let (legRatioQty, bytes) ← decodeUInt 1 bytes
  pure ({ legPrice, legSecurityId, legOptionDelta, legSide, legRatioQty }, bytes)

@[simp] theorem encode_length (message : RequestLegsGroup) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, LegOptionDelta.encode_length, encodeUInt_length]

theorem encode_length_pos (message : RequestLegsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RequestLegsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [LegOptionDelta.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end RequestLegsGroup

/-- Request Legs Groups -/
structure RequestLegsGroups where
  blockLength : BitVec 16
  requestLegsGroup : Bounded 1 RequestLegsGroup
  deriving DecidableEq, Repr

namespace RequestLegsGroups

def encode (message : RequestLegsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.requestLegsGroup.val.length)
    ++ encodeMany RequestLegsGroup.encode message.requestLegsGroup.val

def decode (bytes : List UInt8) : Option (RequestLegsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (requestLegsGroup_, bytes) ← decodeMany RequestLegsGroup.decode numInGroup.toNat bytes
  if fits_requestLegsGroup : requestLegsGroup_.length < 256 ^ 1 then
    pure ({ blockLength, requestLegsGroup := ⟨requestLegsGroup_, fits_requestLegsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : RequestLegsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : RequestLegsGroups) : (encode message).length ≤ 4848 := by
  have bound_requestLegsGroup := message.requestLegsGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const RequestLegsGroup.encode 19 RequestLegsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : RequestLegsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 RequestLegsGroup.encode RequestLegsGroup.decode RequestLegsGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.requestLegsGroup.length_lt, ↓reduceDIte]
  rfl

end RequestLegsGroups

/-- Broken Dates Request Group: 4 bytes -/
structure BrokenDatesRequestGroup where
  brokenDateStart : BitVec 16
  brokenDateEnd : BitVec 16
  deriving DecidableEq, Repr

namespace BrokenDatesRequestGroup

def encode (message : BrokenDatesRequestGroup) : List UInt8 :=
  encodeUIntLE 2 message.brokenDateStart
    ++ encodeUIntLE 2 message.brokenDateEnd

def decode (bytes : List UInt8) : Option (BrokenDatesRequestGroup × List UInt8) := do
  let (brokenDateStart, bytes) ← decodeUIntLE 2 bytes
  let (brokenDateEnd, bytes) ← decodeUIntLE 2 bytes
  pure ({ brokenDateStart, brokenDateEnd }, bytes)

@[simp] theorem encode_length (message : BrokenDatesRequestGroup) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : BrokenDatesRequestGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BrokenDatesRequestGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end BrokenDatesRequestGroup

/-- Broken Dates Request Groups -/
structure BrokenDatesRequestGroups where
  blockLength : BitVec 16
  brokenDatesRequestGroup : Bounded 1 BrokenDatesRequestGroup
  deriving DecidableEq, Repr

namespace BrokenDatesRequestGroups

def encode (message : BrokenDatesRequestGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.brokenDatesRequestGroup.val.length)
    ++ encodeMany BrokenDatesRequestGroup.encode message.brokenDatesRequestGroup.val

def decode (bytes : List UInt8) : Option (BrokenDatesRequestGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (brokenDatesRequestGroup_, bytes) ← decodeMany BrokenDatesRequestGroup.decode numInGroup.toNat bytes
  if fits_brokenDatesRequestGroup : brokenDatesRequestGroup_.length < 256 ^ 1 then
    pure ({ blockLength, brokenDatesRequestGroup := ⟨brokenDatesRequestGroup_, fits_brokenDatesRequestGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : BrokenDatesRequestGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BrokenDatesRequestGroups) : (encode message).length ≤ 1023 := by
  have bound_brokenDatesRequestGroup := message.brokenDatesRequestGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const BrokenDatesRequestGroup.encode 4 BrokenDatesRequestGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : BrokenDatesRequestGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 BrokenDatesRequestGroup.encode BrokenDatesRequestGroup.decode BrokenDatesRequestGroup.decode_encode]
  simp only [Option.bind_some]
  simp only [message.brokenDatesRequestGroup.length_lt, ↓reduceDIte]
  rfl

end BrokenDatesRequestGroups

/-- Security Definition Request -/
structure SecurityDefinitionRequest where
  partyDetailsListReqId : BitVec 64
  securityReqId : BitVec 64
  manualOrderIndicator : BitVec 8
  seqNum : BitVec 32
  senderIdOptional : Alpha 20
  sendingTimeEpoch : BitVec 64
  securitySubType : Alpha 8
  location : Alpha 5
  startDate : BitVec 16
  endDate : BitVec 16
  maxNoOfSubstitutions : BitVec 8
  sourceRepoId : BitVec 32
  brokenDateTermType : BitVec 8
  requestLegsGroups : RequestLegsGroups
  brokenDatesRequestGroups : BrokenDatesRequestGroups
  deriving DecidableEq, Repr

namespace SecurityDefinitionRequest

def encode (message : SecurityDefinitionRequest) : List UInt8 :=
  encodeUIntLE 8 message.partyDetailsListReqId
    ++ encodeUIntLE 8 message.securityReqId
    ++ encodeUInt 1 message.manualOrderIndicator
    ++ encodeUIntLE 4 message.seqNum
    ++ Alpha.encode message.senderIdOptional
    ++ encodeUIntLE 8 message.sendingTimeEpoch
    ++ Alpha.encode message.securitySubType
    ++ Alpha.encode message.location
    ++ encodeUIntLE 2 message.startDate
    ++ encodeUIntLE 2 message.endDate
    ++ encodeUInt 1 message.maxNoOfSubstitutions
    ++ encodeUIntLE 4 message.sourceRepoId
    ++ encodeUInt 1 message.brokenDateTermType
    ++ RequestLegsGroups.encode message.requestLegsGroups
    ++ BrokenDatesRequestGroups.encode message.brokenDatesRequestGroups

def decode (bytes : List UInt8) : Option (SecurityDefinitionRequest × List UInt8) := do
  let (partyDetailsListReqId, bytes) ← decodeUIntLE 8 bytes
  let (securityReqId, bytes) ← decodeUIntLE 8 bytes
  let (manualOrderIndicator, bytes) ← decodeUInt 1 bytes
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (senderIdOptional, bytes) ← Alpha.decode 20 bytes
  let (sendingTimeEpoch, bytes) ← decodeUIntLE 8 bytes
  let (securitySubType, bytes) ← Alpha.decode 8 bytes
  let (location, bytes) ← Alpha.decode 5 bytes
  let (startDate, bytes) ← decodeUIntLE 2 bytes
  let (endDate, bytes) ← decodeUIntLE 2 bytes
  let (maxNoOfSubstitutions, bytes) ← decodeUInt 1 bytes
  let (sourceRepoId, bytes) ← decodeUIntLE 4 bytes
  let (brokenDateTermType, bytes) ← decodeUInt 1 bytes
  let (requestLegsGroups, bytes) ← RequestLegsGroups.decode bytes
  let (brokenDatesRequestGroups, bytes) ← BrokenDatesRequestGroups.decode bytes
  pure ({ partyDetailsListReqId, securityReqId, manualOrderIndicator, seqNum, senderIdOptional, sendingTimeEpoch, securitySubType, location, startDate, endDate, maxNoOfSubstitutions, sourceRepoId, brokenDateTermType, requestLegsGroups, brokenDatesRequestGroups }, bytes)

theorem encode_length_pos (message : SecurityDefinitionRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SecurityDefinitionRequest) : (encode message).length ≤ 5943 := by
  have bound_requestLegsGroups := RequestLegsGroups.encode_length_le message.requestLegsGroups
  have bound_brokenDatesRequestGroups := BrokenDatesRequestGroups.encode_length_le message.brokenDatesRequestGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : SecurityDefinitionRequest) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [RequestLegsGroups.decode_encode]
  simp only [Option.bind_some]
  rw [BrokenDatesRequestGroups.decode_encode, Option.bind_some]
  rfl

end SecurityDefinitionRequest

/-- Any Client Payload, selected by Template Id -/
inductive ClientPayload where
  | negotiate (message : Negotiate) -- 500
  | establish (message : Establish) -- 503
  | sequence (message : Sequence) -- 506
  | terminate (message : Terminate) -- 507
  | retransmitRequest (message : RetransmitRequest) -- 508
  | newOrderSingle (message : NewOrderSingle) -- 514
  | orderCancelReplaceRequest (message : OrderCancelReplaceRequest) -- 515
  | orderCancelRequest (message : OrderCancelRequest) -- 516
  | massQuote (message : MassQuote) -- 517
  | partyDetailsDefinitionRequest (message : PartyDetailsDefinitionRequest) -- 518
  | quoteCancel (message : QuoteCancel) -- 528
  | orderMassActionRequest (message : OrderMassActionRequest) -- 529
  | orderMassStatusRequest (message : OrderMassStatusRequest) -- 530
  | orderStatusRequest (message : OrderStatusRequest) -- 533
  | partyDetailsListRequest (message : PartyDetailsListRequest) -- 537
  | requestForQuote (message : RequestForQuote) -- 543
  | newOrderCross (message : NewOrderCross) -- 544
  | securityDefinitionRequest (message : SecurityDefinitionRequest) -- 560
  deriving DecidableEq, Repr

namespace ClientPayload

/-- The Template Id each message is sent under -/
def tag : ClientPayload → BitVec 16
  | .negotiate _ => 500
  | .establish _ => 503
  | .sequence _ => 506
  | .terminate _ => 507
  | .retransmitRequest _ => 508
  | .newOrderSingle _ => 514
  | .orderCancelReplaceRequest _ => 515
  | .orderCancelRequest _ => 516
  | .massQuote _ => 517
  | .partyDetailsDefinitionRequest _ => 518
  | .quoteCancel _ => 528
  | .orderMassActionRequest _ => 529
  | .orderMassStatusRequest _ => 530
  | .orderStatusRequest _ => 533
  | .partyDetailsListRequest _ => 537
  | .requestForQuote _ => 543
  | .newOrderCross _ => 544
  | .securityDefinitionRequest _ => 560

def encode : ClientPayload → List UInt8
  | .negotiate message => Negotiate.encode message
  | .establish message => Establish.encode message
  | .sequence message => Sequence.encode message
  | .terminate message => Terminate.encode message
  | .retransmitRequest message => RetransmitRequest.encode message
  | .newOrderSingle message => NewOrderSingle.encode message
  | .orderCancelReplaceRequest message => OrderCancelReplaceRequest.encode message
  | .orderCancelRequest message => OrderCancelRequest.encode message
  | .massQuote message => MassQuote.encode message
  | .partyDetailsDefinitionRequest message => PartyDetailsDefinitionRequest.encode message
  | .quoteCancel message => QuoteCancel.encode message
  | .orderMassActionRequest message => OrderMassActionRequest.encode message
  | .orderMassStatusRequest message => OrderMassStatusRequest.encode message
  | .orderStatusRequest message => OrderStatusRequest.encode message
  | .partyDetailsListRequest message => PartyDetailsListRequest.encode message
  | .requestForQuote message => RequestForQuote.encode message
  | .newOrderCross message => NewOrderCross.encode message
  | .securityDefinitionRequest message => SecurityDefinitionRequest.encode message

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (ClientPayload × List UInt8) :=
  if tag = 500 then (Negotiate.decode bytes).map fun (message, rest) => (.negotiate message, rest)
  else if tag = 503 then (Establish.decode bytes).map fun (message, rest) => (.establish message, rest)
  else if tag = 506 then (Sequence.decode bytes).map fun (message, rest) => (.sequence message, rest)
  else if tag = 507 then (Terminate.decode bytes).map fun (message, rest) => (.terminate message, rest)
  else if tag = 508 then (RetransmitRequest.decode bytes).map fun (message, rest) => (.retransmitRequest message, rest)
  else if tag = 514 then (NewOrderSingle.decode bytes).map fun (message, rest) => (.newOrderSingle message, rest)
  else if tag = 515 then (OrderCancelReplaceRequest.decode bytes).map fun (message, rest) => (.orderCancelReplaceRequest message, rest)
  else if tag = 516 then (OrderCancelRequest.decode bytes).map fun (message, rest) => (.orderCancelRequest message, rest)
  else if tag = 517 then (MassQuote.decode bytes).map fun (message, rest) => (.massQuote message, rest)
  else if tag = 518 then (PartyDetailsDefinitionRequest.decode bytes).map fun (message, rest) => (.partyDetailsDefinitionRequest message, rest)
  else if tag = 528 then (QuoteCancel.decode bytes).map fun (message, rest) => (.quoteCancel message, rest)
  else if tag = 529 then (OrderMassActionRequest.decode bytes).map fun (message, rest) => (.orderMassActionRequest message, rest)
  else if tag = 530 then (OrderMassStatusRequest.decode bytes).map fun (message, rest) => (.orderMassStatusRequest message, rest)
  else if tag = 533 then (OrderStatusRequest.decode bytes).map fun (message, rest) => (.orderStatusRequest message, rest)
  else if tag = 537 then (PartyDetailsListRequest.decode bytes).map fun (message, rest) => (.partyDetailsListRequest message, rest)
  else if tag = 543 then (RequestForQuote.decode bytes).map fun (message, rest) => (.requestForQuote message, rest)
  else if tag = 544 then (NewOrderCross.decode bytes).map fun (message, rest) => (.newOrderCross message, rest)
  else if tag = 560 then (SecurityDefinitionRequest.decode bytes).map fun (message, rest) => (.securityDefinitionRequest message, rest)
  else none

@[simp] theorem decode_encode (message : ClientPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ClientPayload

/-- Client Simple Open Frame -/
structure ClientSimpleOpenFrame where
  encodingType : BitVec 16
  blockLength : BitVec 16
  schemaId : BitVec 16
  version : BitVec 16
  clientPayload : ClientPayload
  deriving DecidableEq, Repr

namespace ClientSimpleOpenFrame

def encodeBody (message : ClientSimpleOpenFrame) : List UInt8 :=
  encodeUIntLE 2 message.encodingType
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUIntLE 2 (ClientPayload.tag message.clientPayload)
    ++ encodeUIntLE 2 message.schemaId
    ++ encodeUIntLE 2 message.version
    ++ ClientPayload.encode message.clientPayload

def decodeBody (bytes : List UInt8) : Option (ClientSimpleOpenFrame × List UInt8) := do
  let (encodingType, bytes) ← decodeUIntLE 2 bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (templateId, bytes) ← decodeUIntLE 2 bytes
  let (schemaId, bytes) ← decodeUIntLE 2 bytes
  let (version, bytes) ← decodeUIntLE 2 bytes
  let (clientPayload, bytes) ← ClientPayload.decode templateId bytes
  pure ({ encodingType, blockLength, schemaId, version, clientPayload }, bytes)

theorem decodeBody_encodeBody (message : ClientSimpleOpenFrame) (rest : List UInt8) :
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
  rw [ClientPayload.decode_encode, Option.bind_some]
  rfl

/-- Size rule: Message Length counts the bytes after it plus 2, so it is written from the body; the body has no bound the prefix must fit, so it is read by its content and the prefix is not checked -/
def encode (message : ClientSimpleOpenFrame) : List UInt8 :=
  encodeUIntLE 2 (BitVec.ofNat (8 * 2) ((encodeBody message).length + 2))
    ++ encodeBody message

def decode (bytes : List UInt8) : Option (ClientSimpleOpenFrame × List UInt8) := do
  let (_, bytes) ← decodeUIntLE 2 bytes
  decodeBody bytes

@[simp] theorem decode_encode (message : ClientSimpleOpenFrame) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  exact decodeBody_encodeBody message rest

theorem encode_length_pos (message : ClientSimpleOpenFrame) : (encode message).length > 0 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]
  omega

end ClientSimpleOpenFrame

/-- Client Packet -/
structure ClientPacket where
  clientSimpleOpenFrame : List ClientSimpleOpenFrame
  deriving DecidableEq, Repr

namespace ClientPacket

def encode (message : ClientPacket) : List UInt8 :=
  encodeMany ClientSimpleOpenFrame.encode message.clientSimpleOpenFrame

def decode (bytes : List UInt8) : Option ClientPacket := do
  let clientSimpleOpenFrame ← decodeAll ClientSimpleOpenFrame.decode bytes.length bytes
  pure { clientSimpleOpenFrame }

theorem decode_encode (message : ClientPacket) : decode (encode message) = some message := by
  unfold decode encode
  simp only [Option.bind_eq_bind]
  rw [decodeAll_encodeMany ClientSimpleOpenFrame.encode ClientSimpleOpenFrame.decode ClientSimpleOpenFrame.decode_encode ClientSimpleOpenFrame.encode_length_pos message.clientSimpleOpenFrame _ (encodeMany_length_ge ClientSimpleOpenFrame.encode ClientSimpleOpenFrame.encode_length_pos message.clientSimpleOpenFrame), Option.bind_some]
  rfl

end ClientPacket

end Omi.CmeGlobexIlink3SbeV89Client
