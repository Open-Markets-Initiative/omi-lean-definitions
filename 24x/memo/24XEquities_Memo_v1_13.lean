import Omi.Wire

/-!
# 24 National Exchange Members Orders v1.13

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Exec Inst is a bit field set, proven as its 2 byte integer rather than bit by bit.

Note: Sbe Message is not framed: its size rule is not the length plus a constant the frame proof covers.

Note: Sbe Message is not framed: its size rule is not the length plus a constant the frame proof covers.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.N24x24xequitiesMemoSbeV113

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x31, 0x32, 0x35, 0x36]

inductive Side where
  | buy -- Buy
  | sell -- Sell
  | sellShort -- Sell Short
  | sellShortExempt -- Sell Short Exempt
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buy => 0x31
  | .sell => 0x32
  | .sellShort => 0x35
  | .sellShortExempt => 0x36
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x31 then .buy
  else if byte = 0x32 then .sell
  else if byte = 0x35 then .sellShort
  else .sellShortExempt

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | sellShort => decide
  | sellShortExempt => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Side) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Side × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Side) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Side) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Side

/-- Ord Type: one byte code -/
def OrdType.codes : List UInt8 :=
  [0x31, 0x32, 0x50]

inductive OrdType where
  | market -- Market
  | limit -- Limit
  | pegged -- Pegged
  | unlisted (byte : { byte : UInt8 // byte ∉ OrdType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrdType

def toByte : OrdType → UInt8
  | .market => 0x31
  | .limit => 0x32
  | .pegged => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrdType :=
  if byte = 0x31 then .market
  else if byte = 0x32 then .limit
  else .pegged

def ofByte (byte : UInt8) : OrdType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrdType) : ofByte value.toByte = value := by
  cases value with
  | market => decide
  | limit => decide
  | pegged => decide
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

/-- Time In Force: one byte code -/
def TimeInForce.codes : List UInt8 :=
  [0x30, 0x33, 0x34, 0x41, 0x46]

inductive TimeInForce where
  | day -- Day
  | immediateOrCancel -- Immediate Or Cancel
  | fillOrKill -- Fill Or Kill
  | goodForTime -- Good For Time
  | regularHoursOnly -- Regular Hours Only
  | unlisted (byte : { byte : UInt8 // byte ∉ TimeInForce.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TimeInForce

def toByte : TimeInForce → UInt8
  | .day => 0x30
  | .immediateOrCancel => 0x33
  | .fillOrKill => 0x34
  | .goodForTime => 0x41
  | .regularHoursOnly => 0x46
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TimeInForce :=
  if byte = 0x30 then .day
  else if byte = 0x33 then .immediateOrCancel
  else if byte = 0x34 then .fillOrKill
  else if byte = 0x41 then .goodForTime
  else .regularHoursOnly

def ofByte (byte : UInt8) : TimeInForce :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TimeInForce) : ofByte value.toByte = value := by
  cases value with
  | day => decide
  | immediateOrCancel => decide
  | fillOrKill => decide
  | goodForTime => decide
  | regularHoursOnly => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TimeInForce) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TimeInForce × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TimeInForce) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TimeInForce) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TimeInForce

/-- Order Capacity: one byte code -/
def OrderCapacity.codes : List UInt8 :=
  [0x41, 0x50, 0x52]

inductive OrderCapacity where
  | agency -- Agency
  | principal -- Principal
  | risklessPrincipal -- Riskless Principal
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderCapacity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderCapacity

def toByte : OrderCapacity → UInt8
  | .agency => 0x41
  | .principal => 0x50
  | .risklessPrincipal => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderCapacity :=
  if byte = 0x41 then .agency
  else if byte = 0x50 then .principal
  else .risklessPrincipal

def ofByte (byte : UInt8) : OrderCapacity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderCapacity) : ofByte value.toByte = value := by
  cases value with
  | agency => decide
  | principal => decide
  | risklessPrincipal => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderCapacity) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderCapacity × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderCapacity) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OrderCapacity) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderCapacity

/-- Display Method: one byte code -/
def DisplayMethod.codes : List UInt8 :=
  [0x31, 0x33, 0x34]

inductive DisplayMethod where
  | initial -- Initial
  | random -- Random
  | undisclosed -- Undisclosed
  | unlisted (byte : { byte : UInt8 // byte ∉ DisplayMethod.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DisplayMethod

def toByte : DisplayMethod → UInt8
  | .initial => 0x31
  | .random => 0x33
  | .undisclosed => 0x34
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DisplayMethod :=
  if byte = 0x31 then .initial
  else if byte = 0x33 then .random
  else .undisclosed

def ofByte (byte : UInt8) : DisplayMethod :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DisplayMethod) : ofByte value.toByte = value := by
  cases value with
  | initial => decide
  | random => decide
  | undisclosed => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DisplayMethod) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DisplayMethod × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DisplayMethod) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : DisplayMethod) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DisplayMethod

/-- Side Optional: one byte code -/
def SideOptional.codes : List UInt8 :=
  [0x31, 0x32, 0x35, 0x36]

inductive SideOptional where
  | buy -- Buy
  | sell -- Sell
  | sellShort -- Sell Short
  | sellShortExempt -- Sell Short Exempt
  | unlisted (byte : { byte : UInt8 // byte ∉ SideOptional.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SideOptional

def toByte : SideOptional → UInt8
  | .buy => 0x31
  | .sell => 0x32
  | .sellShort => 0x35
  | .sellShortExempt => 0x36
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SideOptional :=
  if byte = 0x31 then .buy
  else if byte = 0x32 then .sell
  else if byte = 0x35 then .sellShort
  else .sellShortExempt

def ofByte (byte : UInt8) : SideOptional :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SideOptional) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | sellShort => decide
  | sellShortExempt => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SideOptional) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SideOptional × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SideOptional) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SideOptional) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SideOptional

/-- Ord Status: one byte code -/
def OrdStatus.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x34, 0x36, 0x38, 0x41, 0x45, 0x43]

inductive OrdStatus where
  | new -- New
  | partialFilled -- Partial Filled
  | filled -- Filled
  | canceled -- Canceled
  | pendingCancel -- Pending Cancel
  | rejected -- Rejected
  | pendingNew -- Pending New
  | pendingReplace -- Pending Replace
  | expired -- Expired
  | unlisted (byte : { byte : UInt8 // byte ∉ OrdStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrdStatus

def toByte : OrdStatus → UInt8
  | .new => 0x30
  | .partialFilled => 0x31
  | .filled => 0x32
  | .canceled => 0x34
  | .pendingCancel => 0x36
  | .rejected => 0x38
  | .pendingNew => 0x41
  | .pendingReplace => 0x45
  | .expired => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrdStatus :=
  if byte = 0x30 then .new
  else if byte = 0x31 then .partialFilled
  else if byte = 0x32 then .filled
  else if byte = 0x34 then .canceled
  else if byte = 0x36 then .pendingCancel
  else if byte = 0x38 then .rejected
  else if byte = 0x41 then .pendingNew
  else if byte = 0x45 then .pendingReplace
  else .expired

def ofByte (byte : UInt8) : OrdStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrdStatus) : ofByte value.toByte = value := by
  cases value with
  | new => decide
  | partialFilled => decide
  | filled => decide
  | canceled => decide
  | pendingCancel => decide
  | rejected => decide
  | pendingNew => decide
  | pendingReplace => decide
  | expired => decide
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

/-- Cxl Rej Response To: one byte code -/
def CxlRejResponseTo.codes : List UInt8 :=
  [0x31, 0x32]

inductive CxlRejResponseTo where
  | orderCancelRequest -- Order Cancel Request
  | orderCancelReplaceRequest -- Order Cancel Replace Request
  | unlisted (byte : { byte : UInt8 // byte ∉ CxlRejResponseTo.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CxlRejResponseTo

def toByte : CxlRejResponseTo → UInt8
  | .orderCancelRequest => 0x31
  | .orderCancelReplaceRequest => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CxlRejResponseTo :=
  if byte = 0x31 then .orderCancelRequest
  else .orderCancelReplaceRequest

def ofByte (byte : UInt8) : CxlRejResponseTo :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CxlRejResponseTo) : ofByte value.toByte = value := by
  cases value with
  | orderCancelRequest => decide
  | orderCancelReplaceRequest => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CxlRejResponseTo) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CxlRejResponseTo × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CxlRejResponseTo) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CxlRejResponseTo) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CxlRejResponseTo

/-- Supported Request Mode: one byte code -/
def SupportedRequestMode.codes : List UInt8 :=
  [0x53, 0x52, 0x54]

inductive SupportedRequestMode where
  | stream -- Stream
  | replay -- Replay
  | snapshotMode -- Snapshot Mode
  | unlisted (byte : { byte : UInt8 // byte ∉ SupportedRequestMode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SupportedRequestMode

def toByte : SupportedRequestMode → UInt8
  | .stream => 0x53
  | .replay => 0x52
  | .snapshotMode => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SupportedRequestMode :=
  if byte = 0x53 then .stream
  else if byte = 0x52 then .replay
  else .snapshotMode

def ofByte (byte : UInt8) : SupportedRequestMode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SupportedRequestMode) : ofByte value.toByte = value := by
  cases value with
  | stream => decide
  | replay => decide
  | snapshotMode => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SupportedRequestMode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SupportedRequestMode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SupportedRequestMode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SupportedRequestMode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SupportedRequestMode

/-- Login Reject Code: one byte code -/
def LoginRejectCode.codes : List UInt8 :=
  [0x54, 0x55, 0x56, 0x41]

inductive LoginRejectCode where
  | malformedToken -- Malformed Token
  | tokenTypeUnsupported -- Token Type Unsupported
  | tokenTypeInvalid -- Token Type Invalid
  | authorizationFailed -- Authorization Failed
  | unlisted (byte : { byte : UInt8 // byte ∉ LoginRejectCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LoginRejectCode

def toByte : LoginRejectCode → UInt8
  | .malformedToken => 0x54
  | .tokenTypeUnsupported => 0x55
  | .tokenTypeInvalid => 0x56
  | .authorizationFailed => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LoginRejectCode :=
  if byte = 0x54 then .malformedToken
  else if byte = 0x55 then .tokenTypeUnsupported
  else if byte = 0x56 then .tokenTypeInvalid
  else .authorizationFailed

def ofByte (byte : UInt8) : LoginRejectCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LoginRejectCode) : ofByte value.toByte = value := by
  cases value with
  | malformedToken => decide
  | tokenTypeUnsupported => decide
  | tokenTypeInvalid => decide
  | authorizationFailed => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LoginRejectCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LoginRejectCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LoginRejectCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LoginRejectCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LoginRejectCode

/-- Replay Reject Code: one byte code -/
def ReplayRejectCode.codes : List UInt8 :=
  [0x52, 0x41, 0x50, 0x53]

inductive ReplayRejectCode where
  | replayRequestsAreNotAllowed -- Replay Requests Are Not Allowed
  | replayAllRequestsAreNotAllowed -- Replay All Requests Are Not Allowed
  | notTheActiveSession -- Not The Active Session
  | sequenceNumberOutOfRange -- Sequence Number Out Of Range
  | unlisted (byte : { byte : UInt8 // byte ∉ ReplayRejectCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ReplayRejectCode

def toByte : ReplayRejectCode → UInt8
  | .replayRequestsAreNotAllowed => 0x52
  | .replayAllRequestsAreNotAllowed => 0x41
  | .notTheActiveSession => 0x50
  | .sequenceNumberOutOfRange => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ReplayRejectCode :=
  if byte = 0x52 then .replayRequestsAreNotAllowed
  else if byte = 0x41 then .replayAllRequestsAreNotAllowed
  else if byte = 0x50 then .notTheActiveSession
  else .sequenceNumberOutOfRange

def ofByte (byte : UInt8) : ReplayRejectCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ReplayRejectCode) : ofByte value.toByte = value := by
  cases value with
  | replayRequestsAreNotAllowed => decide
  | replayAllRequestsAreNotAllowed => decide
  | notTheActiveSession => decide
  | sequenceNumberOutOfRange => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ReplayRejectCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ReplayRejectCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ReplayRejectCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ReplayRejectCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ReplayRejectCode

/-- Stream Reject Code: one byte code -/
def StreamRejectCode.codes : List UInt8 :=
  [0x52, 0x50, 0x53]

inductive StreamRejectCode where
  | streamRequestsAreNotAllowed -- Stream Requests Are Not Allowed
  | notTheActiveSession -- Not The Active Session
  | sequenceNumberOutOfRange -- Sequence Number Out Of Range
  | unlisted (byte : { byte : UInt8 // byte ∉ StreamRejectCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StreamRejectCode

def toByte : StreamRejectCode → UInt8
  | .streamRequestsAreNotAllowed => 0x52
  | .notTheActiveSession => 0x50
  | .sequenceNumberOutOfRange => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StreamRejectCode :=
  if byte = 0x52 then .streamRequestsAreNotAllowed
  else if byte = 0x50 then .notTheActiveSession
  else .sequenceNumberOutOfRange

def ofByte (byte : UInt8) : StreamRejectCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StreamRejectCode) : ofByte value.toByte = value := by
  cases value with
  | streamRequestsAreNotAllowed => decide
  | notTheActiveSession => decide
  | sequenceNumberOutOfRange => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StreamRejectCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StreamRejectCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StreamRejectCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : StreamRejectCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StreamRejectCode

/-- Login Request Message: 2 bytes -/
structure LoginRequestMessage where
  tokenType : Alpha 1
  token : Alpha 1
  deriving DecidableEq, Repr

namespace LoginRequestMessage

def encode (message : LoginRequestMessage) : List UInt8 :=
  Alpha.encode message.tokenType
    ++ (Alpha.encode message.token)

def decode (bytes : List UInt8) : Option (LoginRequestMessage × List UInt8) := do
  let (tokenType, bytes) ← Alpha.decode 1 bytes
  let (token, bytes) ← Alpha.decode 1 bytes
  pure ({ tokenType, token }, bytes)

@[simp] theorem encode_length (message : LoginRequestMessage) : (encode message).length = 2 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : LoginRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LoginRequestMessage

/-- Replay Request Message: 20 bytes -/
structure ReplayRequestMessage where
  sessionId : BitVec 64
  nextSequenceNumber : BitVec 64
  count : BitVec 32
  deriving DecidableEq, Repr

namespace ReplayRequestMessage

def encode (message : ReplayRequestMessage) : List UInt8 :=
  encodeUInt 8 message.sessionId
    ++ (encodeUInt 8 message.nextSequenceNumber
    ++ (encodeUInt 4 message.count))

def decode (bytes : List UInt8) : Option (ReplayRequestMessage × List UInt8) := do
  let (sessionId, bytes) ← decodeUInt 8 bytes
  let (nextSequenceNumber, bytes) ← decodeUInt 8 bytes
  let (count, bytes) ← decodeUInt 4 bytes
  pure ({ sessionId, nextSequenceNumber, count }, bytes)

@[simp] theorem encode_length (message : ReplayRequestMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : ReplayRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReplayRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ReplayRequestMessage

/-- Replay All Request Message: 8 bytes -/
structure ReplayAllRequestMessage where
  sessionId : BitVec 64
  deriving DecidableEq, Repr

namespace ReplayAllRequestMessage

def encode (message : ReplayAllRequestMessage) : List UInt8 :=
  encodeUInt 8 message.sessionId

def decode (bytes : List UInt8) : Option (ReplayAllRequestMessage × List UInt8) := do
  let (sessionId, bytes) ← decodeUInt 8 bytes
  pure ({ sessionId }, bytes)

@[simp] theorem encode_length (message : ReplayAllRequestMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : ReplayAllRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReplayAllRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ReplayAllRequestMessage

/-- Stream Request Message: 16 bytes -/
structure StreamRequestMessage where
  sessionId : BitVec 64
  nextSequenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace StreamRequestMessage

def encode (message : StreamRequestMessage) : List UInt8 :=
  encodeUInt 8 message.sessionId
    ++ (encodeUInt 8 message.nextSequenceNumber)

def decode (bytes : List UInt8) : Option (StreamRequestMessage × List UInt8) := do
  let (sessionId, bytes) ← decodeUInt 8 bytes
  let (nextSequenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ sessionId, nextSequenceNumber }, bytes)

@[simp] theorem encode_length (message : StreamRequestMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : StreamRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StreamRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end StreamRequestMessage

/-- Parties Group: 18 bytes -/
structure PartiesGroup where
  partyIdNewOrderSinglePartyId : Alpha 16
  partyIdSource : Alpha 1
  partyRole : BitVec 8
  deriving DecidableEq, Repr

namespace PartiesGroup

def encode (message : PartiesGroup) : List UInt8 :=
  Alpha.encode message.partyIdNewOrderSinglePartyId
    ++ (Alpha.encode message.partyIdSource
    ++ (encodeUInt 1 message.partyRole))

def decode (bytes : List UInt8) : Option (PartiesGroup × List UInt8) := do
  let (partyIdNewOrderSinglePartyId, bytes) ← Alpha.decode 16 bytes
  let (partyIdSource, bytes) ← Alpha.decode 1 bytes
  let (partyRole, bytes) ← decodeUInt 1 bytes
  pure ({ partyIdNewOrderSinglePartyId, partyIdSource, partyRole }, bytes)

@[simp] theorem encode_length (message : PartiesGroup) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : PartiesGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PartiesGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end PartiesGroup

/-- Parties Groups -/
structure PartiesGroups where
  blockLengthShort : BitVec 8
  partiesGroup : Bounded 1 PartiesGroup
  deriving DecidableEq, Repr

namespace PartiesGroups

def encode (message : PartiesGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.partiesGroup.val.length)
    ++ (encodeMany PartiesGroup.encode message.partiesGroup.val))

def decode (bytes : List UInt8) : Option (PartiesGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (partiesGroup_, bytes) ← decodeMany PartiesGroup.decode numInGroup.toNat bytes
  if fits_partiesGroup : partiesGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, partiesGroup := ⟨partiesGroup_, fits_partiesGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : PartiesGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : PartiesGroups) : (encode message).length ≤ 4592 := by
  have bound_partiesGroup := message.partiesGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const PartiesGroup.encode 18 PartiesGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : PartiesGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 PartiesGroup.encode PartiesGroup.decode PartiesGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.partiesGroup.length_lt]
  rfl

end PartiesGroups

/-- New Order Single Message -/
structure NewOrderSingleMessage where
  clordid : Alpha 16
  symbol : Alpha 6
  symbolSfx : Alpha 6
  side : Side
  orderQty : BitVec 32
  ordType : OrdType
  price : BitVec 64
  timeInForce : TimeInForce
  orderCapacity : OrderCapacity
  custOrderCapacityOptional : BitVec 8
  execInst : BitVec 16
  pegOffsetValue : BitVec 64
  pegPriceType : BitVec 8
  expireTime : BitVec 64
  minQty : BitVec 32
  displayQty : BitVec 32
  displayMethod : DisplayMethod
  reserveReplenishTiming : BitVec 8
  displayMinIncr : BitVec 32
  locateReqd : Alpha 1
  repriceFrequency : BitVec 8
  repriceBehavior : BitVec 8
  cancelGroupId : BitVec 16
  stpGroupId : BitVec 16
  selfTradePrevention : BitVec 8
  riskGroupId : BitVec 16
  linkIdOptional : Alpha 4
  locateBrokerOptional : Alpha 4
  partiesGroups : PartiesGroups
  deriving DecidableEq, Repr

namespace NewOrderSingleMessage

def encode (message : NewOrderSingleMessage) : List UInt8 :=
  Alpha.encode message.clordid
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.symbolSfx
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.orderQty
    ++ (OrdType.encode message.ordType
    ++ (encodeUInt 8 message.price
    ++ (TimeInForce.encode message.timeInForce
    ++ (OrderCapacity.encode message.orderCapacity
    ++ (encodeUInt 1 message.custOrderCapacityOptional
    ++ (encodeUInt 2 message.execInst
    ++ (encodeUInt 8 message.pegOffsetValue
    ++ (encodeUInt 1 message.pegPriceType
    ++ (encodeUInt 8 message.expireTime
    ++ (encodeUInt 4 message.minQty
    ++ (encodeUInt 4 message.displayQty
    ++ (DisplayMethod.encode message.displayMethod
    ++ (encodeUInt 1 message.reserveReplenishTiming
    ++ (encodeUInt 4 message.displayMinIncr
    ++ (Alpha.encode message.locateReqd
    ++ (encodeUInt 1 message.repriceFrequency
    ++ (encodeUInt 1 message.repriceBehavior
    ++ (encodeUInt 2 message.cancelGroupId
    ++ (encodeUInt 2 message.stpGroupId
    ++ (encodeUInt 1 message.selfTradePrevention
    ++ (encodeUInt 2 message.riskGroupId
    ++ (Alpha.encode message.linkIdOptional
    ++ (Alpha.encode message.locateBrokerOptional
    ++ (PartiesGroups.encode message.partiesGroups))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (NewOrderSingleMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 16 bytes
  let (symbol, bytes) ← Alpha.decode 6 bytes
  let (symbolSfx, bytes) ← Alpha.decode 6 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderQty, bytes) ← decodeUInt 4 bytes
  let (ordType, bytes) ← OrdType.decode bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (timeInForce, bytes) ← TimeInForce.decode bytes
  let (orderCapacity, bytes) ← OrderCapacity.decode bytes
  let (custOrderCapacityOptional, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUInt 2 bytes
  let (pegOffsetValue, bytes) ← decodeUInt 8 bytes
  let (pegPriceType, bytes) ← decodeUInt 1 bytes
  let (expireTime, bytes) ← decodeUInt 8 bytes
  let (minQty, bytes) ← decodeUInt 4 bytes
  let (displayQty, bytes) ← decodeUInt 4 bytes
  let (displayMethod, bytes) ← DisplayMethod.decode bytes
  let (reserveReplenishTiming, bytes) ← decodeUInt 1 bytes
  let (displayMinIncr, bytes) ← decodeUInt 4 bytes
  let (locateReqd, bytes) ← Alpha.decode 1 bytes
  let (repriceFrequency, bytes) ← decodeUInt 1 bytes
  let (repriceBehavior, bytes) ← decodeUInt 1 bytes
  let (cancelGroupId, bytes) ← decodeUInt 2 bytes
  let (stpGroupId, bytes) ← decodeUInt 2 bytes
  let (selfTradePrevention, bytes) ← decodeUInt 1 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (linkIdOptional, bytes) ← Alpha.decode 4 bytes
  let (locateBrokerOptional, bytes) ← Alpha.decode 4 bytes
  let (partiesGroups, bytes) ← PartiesGroups.decode bytes
  pure ({ clordid, symbol, symbolSfx, side, orderQty, ordType, price, timeInForce, orderCapacity, custOrderCapacityOptional, execInst, pegOffsetValue, pegPriceType, expireTime, minQty, displayQty, displayMethod, reserveReplenishTiming, displayMinIncr, locateReqd, repriceFrequency, repriceBehavior, cancelGroupId, stpGroupId, selfTradePrevention, riskGroupId, linkIdOptional, locateBrokerOptional, partiesGroups }, bytes)

theorem encode_length_pos (message : NewOrderSingleMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : NewOrderSingleMessage) : (encode message).length ≤ 4688 := by
  have bound_partiesGroups := PartiesGroups.encode_length_le message.partiesGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, Side.encode_length, encodeUInt_length, OrdType.encode_length, TimeInForce.encode_length, OrderCapacity.encode_length, DisplayMethod.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : NewOrderSingleMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrdType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TimeInForce.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderCapacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, DisplayMethod.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [PartiesGroups.decode_encode, some_bind]
  rfl

end NewOrderSingleMessage

/-- Order Cancel Replace Request Message: 71 bytes -/
structure OrderCancelReplaceRequestMessage where
  origclordid : Alpha 16
  clordid : Alpha 16
  symbol : Alpha 6
  symbolSfx : Alpha 6
  side : Side
  orderQty : BitVec 32
  ordType : OrdType
  price : BitVec 64
  displayQty : BitVec 32
  locateReqd : Alpha 1
  linkIdOptional : Alpha 4
  locateBrokerOptional : Alpha 4
  deriving DecidableEq, Repr

namespace OrderCancelReplaceRequestMessage

def encode (message : OrderCancelReplaceRequestMessage) : List UInt8 :=
  Alpha.encode message.origclordid
    ++ (Alpha.encode message.clordid
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.symbolSfx
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.orderQty
    ++ (OrdType.encode message.ordType
    ++ (encodeUInt 8 message.price
    ++ (encodeUInt 4 message.displayQty
    ++ (Alpha.encode message.locateReqd
    ++ (Alpha.encode message.linkIdOptional
    ++ (Alpha.encode message.locateBrokerOptional)))))))))))

def decode (bytes : List UInt8) : Option (OrderCancelReplaceRequestMessage × List UInt8) := do
  let (origclordid, bytes) ← Alpha.decode 16 bytes
  let (clordid, bytes) ← Alpha.decode 16 bytes
  let (symbol, bytes) ← Alpha.decode 6 bytes
  let (symbolSfx, bytes) ← Alpha.decode 6 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderQty, bytes) ← decodeUInt 4 bytes
  let (ordType, bytes) ← OrdType.decode bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (displayQty, bytes) ← decodeUInt 4 bytes
  let (locateReqd, bytes) ← Alpha.decode 1 bytes
  let (linkIdOptional, bytes) ← Alpha.decode 4 bytes
  let (locateBrokerOptional, bytes) ← Alpha.decode 4 bytes
  pure ({ origclordid, clordid, symbol, symbolSfx, side, orderQty, ordType, price, displayQty, locateReqd, linkIdOptional, locateBrokerOptional }, bytes)

@[simp] theorem encode_length (message : OrderCancelReplaceRequestMessage) : (encode message).length = 71 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, Side.encode_length, encodeUInt_length, OrdType.encode_length]

theorem encode_length_pos (message : OrderCancelReplaceRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancelReplaceRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrdType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderCancelReplaceRequestMessage

/-- Order Cancel Request Message: 52 bytes -/
structure OrderCancelRequestMessage where
  origclordidOptional : Alpha 16
  orderIdOptional : BitVec 64
  clordid : Alpha 16
  symbol : Alpha 6
  symbolSfx : Alpha 6
  deriving DecidableEq, Repr

namespace OrderCancelRequestMessage

def encode (message : OrderCancelRequestMessage) : List UInt8 :=
  Alpha.encode message.origclordidOptional
    ++ (encodeUInt 8 message.orderIdOptional
    ++ (Alpha.encode message.clordid
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.symbolSfx))))

def decode (bytes : List UInt8) : Option (OrderCancelRequestMessage × List UInt8) := do
  let (origclordidOptional, bytes) ← Alpha.decode 16 bytes
  let (orderIdOptional, bytes) ← decodeUInt 8 bytes
  let (clordid, bytes) ← Alpha.decode 16 bytes
  let (symbol, bytes) ← Alpha.decode 6 bytes
  let (symbolSfx, bytes) ← Alpha.decode 6 bytes
  pure ({ origclordidOptional, orderIdOptional, clordid, symbol, symbolSfx }, bytes)

@[simp] theorem encode_length (message : OrderCancelRequestMessage) : (encode message).length = 52 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : OrderCancelRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancelRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderCancelRequestMessage

/-- Mass Cancel Request Message: 47 bytes -/
structure MassCancelRequestMessage where
  clordid : Alpha 16
  symbol : Alpha 6
  symbolSfx : Alpha 6
  sideOptional : SideOptional
  lowerThanPrice : BitVec 64
  higherThanPrice : BitVec 64
  cancelGroupId : BitVec 16
  deriving DecidableEq, Repr

namespace MassCancelRequestMessage

def encode (message : MassCancelRequestMessage) : List UInt8 :=
  Alpha.encode message.clordid
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.symbolSfx
    ++ (SideOptional.encode message.sideOptional
    ++ (encodeUInt 8 message.lowerThanPrice
    ++ (encodeUInt 8 message.higherThanPrice
    ++ (encodeUInt 2 message.cancelGroupId))))))

def decode (bytes : List UInt8) : Option (MassCancelRequestMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 16 bytes
  let (symbol, bytes) ← Alpha.decode 6 bytes
  let (symbolSfx, bytes) ← Alpha.decode 6 bytes
  let (sideOptional, bytes) ← SideOptional.decode bytes
  let (lowerThanPrice, bytes) ← decodeUInt 8 bytes
  let (higherThanPrice, bytes) ← decodeUInt 8 bytes
  let (cancelGroupId, bytes) ← decodeUInt 2 bytes
  pure ({ clordid, symbol, symbolSfx, sideOptional, lowerThanPrice, higherThanPrice, cancelGroupId }, bytes)

@[simp] theorem encode_length (message : MassCancelRequestMessage) : (encode message).length = 47 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, SideOptional.encode_length, encodeUInt_length]

theorem encode_length_pos (message : MassCancelRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassCancelRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SideOptional.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MassCancelRequestMessage

/-- Execution Report Pending New Message -/
structure ExecutionReportPendingNewMessage where
  sendingTime : BitVec 64
  orderId : BitVec 64
  clordid : Alpha 16
  execId : BitVec 64
  ordStatus : OrdStatus
  symbol : Alpha 6
  symbolSfx : Alpha 6
  side : Side
  ordType : OrdType
  orderQty : BitVec 32
  price : BitVec 64
  timeInForce : TimeInForce
  orderCapacity : OrderCapacity
  custOrderCapacity : BitVec 8
  execInst : BitVec 16
  pegOffsetValue : BitVec 64
  pegPriceType : BitVec 8
  expireTime : BitVec 64
  minQty : BitVec 32
  displayQty : BitVec 32
  displayMethod : DisplayMethod
  reserveReplenishTiming : BitVec 8
  displayMinIncr : BitVec 32
  locateReqd : Alpha 1
  repriceFrequency : BitVec 8
  repriceBehavior : BitVec 8
  cancelGroupId : BitVec 16
  stpGroupId : BitVec 16
  selfTradePrevention : BitVec 8
  riskGroupId : BitVec 16
  leavesQty : BitVec 32
  cumQty : BitVec 32
  linkIdOptional : Alpha 4
  locateBrokerOptional : Alpha 4
  partiesGroups : PartiesGroups
  deriving DecidableEq, Repr

namespace ExecutionReportPendingNewMessage

def encode (message : ExecutionReportPendingNewMessage) : List UInt8 :=
  encodeUInt 8 message.sendingTime
    ++ (encodeUInt 8 message.orderId
    ++ (Alpha.encode message.clordid
    ++ (encodeUInt 8 message.execId
    ++ (OrdStatus.encode message.ordStatus
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.symbolSfx
    ++ (Side.encode message.side
    ++ (OrdType.encode message.ordType
    ++ (encodeUInt 4 message.orderQty
    ++ (encodeUInt 8 message.price
    ++ (TimeInForce.encode message.timeInForce
    ++ (OrderCapacity.encode message.orderCapacity
    ++ (encodeUInt 1 message.custOrderCapacity
    ++ (encodeUInt 2 message.execInst
    ++ (encodeUInt 8 message.pegOffsetValue
    ++ (encodeUInt 1 message.pegPriceType
    ++ (encodeUInt 8 message.expireTime
    ++ (encodeUInt 4 message.minQty
    ++ (encodeUInt 4 message.displayQty
    ++ (DisplayMethod.encode message.displayMethod
    ++ (encodeUInt 1 message.reserveReplenishTiming
    ++ (encodeUInt 4 message.displayMinIncr
    ++ (Alpha.encode message.locateReqd
    ++ (encodeUInt 1 message.repriceFrequency
    ++ (encodeUInt 1 message.repriceBehavior
    ++ (encodeUInt 2 message.cancelGroupId
    ++ (encodeUInt 2 message.stpGroupId
    ++ (encodeUInt 1 message.selfTradePrevention
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 4 message.leavesQty
    ++ (encodeUInt 4 message.cumQty
    ++ (Alpha.encode message.linkIdOptional
    ++ (Alpha.encode message.locateBrokerOptional
    ++ (PartiesGroups.encode message.partiesGroups))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ExecutionReportPendingNewMessage × List UInt8) := do
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (clordid, bytes) ← Alpha.decode 16 bytes
  let (execId, bytes) ← decodeUInt 8 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (symbol, bytes) ← Alpha.decode 6 bytes
  let (symbolSfx, bytes) ← Alpha.decode 6 bytes
  let (side, bytes) ← Side.decode bytes
  let (ordType, bytes) ← OrdType.decode bytes
  let (orderQty, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (timeInForce, bytes) ← TimeInForce.decode bytes
  let (orderCapacity, bytes) ← OrderCapacity.decode bytes
  let (custOrderCapacity, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUInt 2 bytes
  let (pegOffsetValue, bytes) ← decodeUInt 8 bytes
  let (pegPriceType, bytes) ← decodeUInt 1 bytes
  let (expireTime, bytes) ← decodeUInt 8 bytes
  let (minQty, bytes) ← decodeUInt 4 bytes
  let (displayQty, bytes) ← decodeUInt 4 bytes
  let (displayMethod, bytes) ← DisplayMethod.decode bytes
  let (reserveReplenishTiming, bytes) ← decodeUInt 1 bytes
  let (displayMinIncr, bytes) ← decodeUInt 4 bytes
  let (locateReqd, bytes) ← Alpha.decode 1 bytes
  let (repriceFrequency, bytes) ← decodeUInt 1 bytes
  let (repriceBehavior, bytes) ← decodeUInt 1 bytes
  let (cancelGroupId, bytes) ← decodeUInt 2 bytes
  let (stpGroupId, bytes) ← decodeUInt 2 bytes
  let (selfTradePrevention, bytes) ← decodeUInt 1 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (leavesQty, bytes) ← decodeUInt 4 bytes
  let (cumQty, bytes) ← decodeUInt 4 bytes
  let (linkIdOptional, bytes) ← Alpha.decode 4 bytes
  let (locateBrokerOptional, bytes) ← Alpha.decode 4 bytes
  let (partiesGroups, bytes) ← PartiesGroups.decode bytes
  pure ({ sendingTime, orderId, clordid, execId, ordStatus, symbol, symbolSfx, side, ordType, orderQty, price, timeInForce, orderCapacity, custOrderCapacity, execInst, pegOffsetValue, pegPriceType, expireTime, minQty, displayQty, displayMethod, reserveReplenishTiming, displayMinIncr, locateReqd, repriceFrequency, repriceBehavior, cancelGroupId, stpGroupId, selfTradePrevention, riskGroupId, leavesQty, cumQty, linkIdOptional, locateBrokerOptional, partiesGroups }, bytes)

theorem encode_length_pos (message : ExecutionReportPendingNewMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ExecutionReportPendingNewMessage) : (encode message).length ≤ 4721 := by
  have bound_partiesGroups := PartiesGroups.encode_length_le message.partiesGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OrdStatus.encode_length, Side.encode_length, OrdType.encode_length, TimeInForce.encode_length, OrderCapacity.encode_length, DisplayMethod.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ExecutionReportPendingNewMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TimeInForce.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderCapacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, DisplayMethod.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [PartiesGroups.decode_encode, some_bind]
  rfl

end ExecutionReportPendingNewMessage

/-- Execution Report New Message -/
structure ExecutionReportNewMessage where
  sendingTime : BitVec 64
  orderId : BitVec 64
  clordid : Alpha 16
  execId : BitVec 64
  ordStatus : OrdStatus
  symbol : Alpha 6
  symbolSfx : Alpha 6
  side : Side
  ordType : OrdType
  orderQty : BitVec 32
  price : BitVec 64
  timeInForce : TimeInForce
  orderCapacity : OrderCapacity
  custOrderCapacity : BitVec 8
  execInst : BitVec 16
  pegOffsetValue : BitVec 64
  pegPriceType : BitVec 8
  expireTime : BitVec 64
  minQty : BitVec 32
  displayQty : BitVec 32
  displayMethod : DisplayMethod
  reserveReplenishTiming : BitVec 8
  displayMinIncr : BitVec 32
  locateReqd : Alpha 1
  repriceFrequency : BitVec 8
  repriceBehavior : BitVec 8
  cancelGroupId : BitVec 16
  stpGroupId : BitVec 16
  selfTradePrevention : BitVec 8
  riskGroupId : BitVec 16
  leavesQty : BitVec 32
  cumQty : BitVec 32
  transactTime : BitVec 64
  linkIdOptional : Alpha 4
  locateBrokerOptional : Alpha 4
  partiesGroups : PartiesGroups
  deriving DecidableEq, Repr

namespace ExecutionReportNewMessage

def encode (message : ExecutionReportNewMessage) : List UInt8 :=
  encodeUInt 8 message.sendingTime
    ++ (encodeUInt 8 message.orderId
    ++ (Alpha.encode message.clordid
    ++ (encodeUInt 8 message.execId
    ++ (OrdStatus.encode message.ordStatus
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.symbolSfx
    ++ (Side.encode message.side
    ++ (OrdType.encode message.ordType
    ++ (encodeUInt 4 message.orderQty
    ++ (encodeUInt 8 message.price
    ++ (TimeInForce.encode message.timeInForce
    ++ (OrderCapacity.encode message.orderCapacity
    ++ (encodeUInt 1 message.custOrderCapacity
    ++ (encodeUInt 2 message.execInst
    ++ (encodeUInt 8 message.pegOffsetValue
    ++ (encodeUInt 1 message.pegPriceType
    ++ (encodeUInt 8 message.expireTime
    ++ (encodeUInt 4 message.minQty
    ++ (encodeUInt 4 message.displayQty
    ++ (DisplayMethod.encode message.displayMethod
    ++ (encodeUInt 1 message.reserveReplenishTiming
    ++ (encodeUInt 4 message.displayMinIncr
    ++ (Alpha.encode message.locateReqd
    ++ (encodeUInt 1 message.repriceFrequency
    ++ (encodeUInt 1 message.repriceBehavior
    ++ (encodeUInt 2 message.cancelGroupId
    ++ (encodeUInt 2 message.stpGroupId
    ++ (encodeUInt 1 message.selfTradePrevention
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 4 message.leavesQty
    ++ (encodeUInt 4 message.cumQty
    ++ (encodeUInt 8 message.transactTime
    ++ (Alpha.encode message.linkIdOptional
    ++ (Alpha.encode message.locateBrokerOptional
    ++ (PartiesGroups.encode message.partiesGroups)))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ExecutionReportNewMessage × List UInt8) := do
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (clordid, bytes) ← Alpha.decode 16 bytes
  let (execId, bytes) ← decodeUInt 8 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (symbol, bytes) ← Alpha.decode 6 bytes
  let (symbolSfx, bytes) ← Alpha.decode 6 bytes
  let (side, bytes) ← Side.decode bytes
  let (ordType, bytes) ← OrdType.decode bytes
  let (orderQty, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (timeInForce, bytes) ← TimeInForce.decode bytes
  let (orderCapacity, bytes) ← OrderCapacity.decode bytes
  let (custOrderCapacity, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUInt 2 bytes
  let (pegOffsetValue, bytes) ← decodeUInt 8 bytes
  let (pegPriceType, bytes) ← decodeUInt 1 bytes
  let (expireTime, bytes) ← decodeUInt 8 bytes
  let (minQty, bytes) ← decodeUInt 4 bytes
  let (displayQty, bytes) ← decodeUInt 4 bytes
  let (displayMethod, bytes) ← DisplayMethod.decode bytes
  let (reserveReplenishTiming, bytes) ← decodeUInt 1 bytes
  let (displayMinIncr, bytes) ← decodeUInt 4 bytes
  let (locateReqd, bytes) ← Alpha.decode 1 bytes
  let (repriceFrequency, bytes) ← decodeUInt 1 bytes
  let (repriceBehavior, bytes) ← decodeUInt 1 bytes
  let (cancelGroupId, bytes) ← decodeUInt 2 bytes
  let (stpGroupId, bytes) ← decodeUInt 2 bytes
  let (selfTradePrevention, bytes) ← decodeUInt 1 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (leavesQty, bytes) ← decodeUInt 4 bytes
  let (cumQty, bytes) ← decodeUInt 4 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (linkIdOptional, bytes) ← Alpha.decode 4 bytes
  let (locateBrokerOptional, bytes) ← Alpha.decode 4 bytes
  let (partiesGroups, bytes) ← PartiesGroups.decode bytes
  pure ({ sendingTime, orderId, clordid, execId, ordStatus, symbol, symbolSfx, side, ordType, orderQty, price, timeInForce, orderCapacity, custOrderCapacity, execInst, pegOffsetValue, pegPriceType, expireTime, minQty, displayQty, displayMethod, reserveReplenishTiming, displayMinIncr, locateReqd, repriceFrequency, repriceBehavior, cancelGroupId, stpGroupId, selfTradePrevention, riskGroupId, leavesQty, cumQty, transactTime, linkIdOptional, locateBrokerOptional, partiesGroups }, bytes)

theorem encode_length_pos (message : ExecutionReportNewMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ExecutionReportNewMessage) : (encode message).length ≤ 4729 := by
  have bound_partiesGroups := PartiesGroups.encode_length_le message.partiesGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OrdStatus.encode_length, Side.encode_length, OrdType.encode_length, TimeInForce.encode_length, OrderCapacity.encode_length, DisplayMethod.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ExecutionReportNewMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TimeInForce.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderCapacity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, DisplayMethod.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [PartiesGroups.decode_encode, some_bind]
  rfl

end ExecutionReportNewMessage

/-- Execution Report Rejected Message -/
structure ExecutionReportRejectedMessage where
  sendingTime : BitVec 64
  clordid : Alpha 16
  execId : BitVec 64
  ordStatus : OrdStatus
  symbol : Alpha 6
  symbolSfx : Alpha 6
  leavesQty : BitVec 32
  cumQty : BitVec 32
  orderRejectReason : BitVec 8
  linkIdOptional : Alpha 4
  partiesGroups : PartiesGroups
  deriving DecidableEq, Repr

namespace ExecutionReportRejectedMessage

def encode (message : ExecutionReportRejectedMessage) : List UInt8 :=
  encodeUInt 8 message.sendingTime
    ++ (Alpha.encode message.clordid
    ++ (encodeUInt 8 message.execId
    ++ (OrdStatus.encode message.ordStatus
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.symbolSfx
    ++ (encodeUInt 4 message.leavesQty
    ++ (encodeUInt 4 message.cumQty
    ++ (encodeUInt 1 message.orderRejectReason
    ++ (Alpha.encode message.linkIdOptional
    ++ (PartiesGroups.encode message.partiesGroups))))))))))

def decode (bytes : List UInt8) : Option (ExecutionReportRejectedMessage × List UInt8) := do
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  let (clordid, bytes) ← Alpha.decode 16 bytes
  let (execId, bytes) ← decodeUInt 8 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (symbol, bytes) ← Alpha.decode 6 bytes
  let (symbolSfx, bytes) ← Alpha.decode 6 bytes
  let (leavesQty, bytes) ← decodeUInt 4 bytes
  let (cumQty, bytes) ← decodeUInt 4 bytes
  let (orderRejectReason, bytes) ← decodeUInt 1 bytes
  let (linkIdOptional, bytes) ← Alpha.decode 4 bytes
  let (partiesGroups, bytes) ← PartiesGroups.decode bytes
  pure ({ sendingTime, clordid, execId, ordStatus, symbol, symbolSfx, leavesQty, cumQty, orderRejectReason, linkIdOptional, partiesGroups }, bytes)

theorem encode_length_pos (message : ExecutionReportRejectedMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ExecutionReportRejectedMessage) : (encode message).length ≤ 4650 := by
  have bound_partiesGroups := PartiesGroups.encode_length_le message.partiesGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OrdStatus.encode_length]
  omega

@[simp] theorem decode_encode (message : ExecutionReportRejectedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [PartiesGroups.decode_encode, some_bind]
  rfl

end ExecutionReportRejectedMessage

/-- Execution Report Trade Message -/
structure ExecutionReportTradeMessage where
  sendingTime : BitVec 64
  orderId : BitVec 64
  clordid : Alpha 16
  execId : BitVec 64
  ordStatus : OrdStatus
  lastQty : BitVec 32
  lastPx : BitVec 64
  leavesQty : BitVec 32
  cumQty : BitVec 32
  transactTime : BitVec 64
  lastLiquidityInd : BitVec 8
  lastMkt : Alpha 4
  trdMatchingId : BitVec 64
  linkIdOptional : Alpha 4
  securityGroup : Alpha 1
  partiesGroups : PartiesGroups
  deriving DecidableEq, Repr

namespace ExecutionReportTradeMessage

def encode (message : ExecutionReportTradeMessage) : List UInt8 :=
  encodeUInt 8 message.sendingTime
    ++ (encodeUInt 8 message.orderId
    ++ (Alpha.encode message.clordid
    ++ (encodeUInt 8 message.execId
    ++ (OrdStatus.encode message.ordStatus
    ++ (encodeUInt 4 message.lastQty
    ++ (encodeUInt 8 message.lastPx
    ++ (encodeUInt 4 message.leavesQty
    ++ (encodeUInt 4 message.cumQty
    ++ (encodeUInt 8 message.transactTime
    ++ (encodeUInt 1 message.lastLiquidityInd
    ++ (Alpha.encode message.lastMkt
    ++ (encodeUInt 8 message.trdMatchingId
    ++ (Alpha.encode message.linkIdOptional
    ++ (Alpha.encode message.securityGroup
    ++ (PartiesGroups.encode message.partiesGroups)))))))))))))))

def decode (bytes : List UInt8) : Option (ExecutionReportTradeMessage × List UInt8) := do
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (clordid, bytes) ← Alpha.decode 16 bytes
  let (execId, bytes) ← decodeUInt 8 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (lastQty, bytes) ← decodeUInt 4 bytes
  let (lastPx, bytes) ← decodeUInt 8 bytes
  let (leavesQty, bytes) ← decodeUInt 4 bytes
  let (cumQty, bytes) ← decodeUInt 4 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (lastLiquidityInd, bytes) ← decodeUInt 1 bytes
  let (lastMkt, bytes) ← Alpha.decode 4 bytes
  let (trdMatchingId, bytes) ← decodeUInt 8 bytes
  let (linkIdOptional, bytes) ← Alpha.decode 4 bytes
  let (securityGroup, bytes) ← Alpha.decode 1 bytes
  let (partiesGroups, bytes) ← PartiesGroups.decode bytes
  pure ({ sendingTime, orderId, clordid, execId, ordStatus, lastQty, lastPx, leavesQty, cumQty, transactTime, lastLiquidityInd, lastMkt, trdMatchingId, linkIdOptional, securityGroup, partiesGroups }, bytes)

theorem encode_length_pos (message : ExecutionReportTradeMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ExecutionReportTradeMessage) : (encode message).length ≤ 4679 := by
  have bound_partiesGroups := PartiesGroups.encode_length_le message.partiesGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OrdStatus.encode_length]
  omega

@[simp] theorem decode_encode (message : ExecutionReportTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [PartiesGroups.decode_encode, some_bind]
  rfl

end ExecutionReportTradeMessage

/-- Execution Report Pending Cancel Message -/
structure ExecutionReportPendingCancelMessage where
  sendingTime : BitVec 64
  orderId : BitVec 64
  clordid : Alpha 16
  origclordidOptional : Alpha 16
  execId : BitVec 64
  symbol : Alpha 6
  symbolSfx : Alpha 6
  ordStatus : OrdStatus
  leavesQty : BitVec 32
  cumQty : BitVec 32
  linkIdOptional : Alpha 4
  partiesGroups : PartiesGroups
  deriving DecidableEq, Repr

namespace ExecutionReportPendingCancelMessage

def encode (message : ExecutionReportPendingCancelMessage) : List UInt8 :=
  encodeUInt 8 message.sendingTime
    ++ (encodeUInt 8 message.orderId
    ++ (Alpha.encode message.clordid
    ++ (Alpha.encode message.origclordidOptional
    ++ (encodeUInt 8 message.execId
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.symbolSfx
    ++ (OrdStatus.encode message.ordStatus
    ++ (encodeUInt 4 message.leavesQty
    ++ (encodeUInt 4 message.cumQty
    ++ (Alpha.encode message.linkIdOptional
    ++ (PartiesGroups.encode message.partiesGroups)))))))))))

def decode (bytes : List UInt8) : Option (ExecutionReportPendingCancelMessage × List UInt8) := do
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (clordid, bytes) ← Alpha.decode 16 bytes
  let (origclordidOptional, bytes) ← Alpha.decode 16 bytes
  let (execId, bytes) ← decodeUInt 8 bytes
  let (symbol, bytes) ← Alpha.decode 6 bytes
  let (symbolSfx, bytes) ← Alpha.decode 6 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (leavesQty, bytes) ← decodeUInt 4 bytes
  let (cumQty, bytes) ← decodeUInt 4 bytes
  let (linkIdOptional, bytes) ← Alpha.decode 4 bytes
  let (partiesGroups, bytes) ← PartiesGroups.decode bytes
  pure ({ sendingTime, orderId, clordid, origclordidOptional, execId, symbol, symbolSfx, ordStatus, leavesQty, cumQty, linkIdOptional, partiesGroups }, bytes)

theorem encode_length_pos (message : ExecutionReportPendingCancelMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ExecutionReportPendingCancelMessage) : (encode message).length ≤ 4673 := by
  have bound_partiesGroups := PartiesGroups.encode_length_le message.partiesGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OrdStatus.encode_length]
  omega

@[simp] theorem decode_encode (message : ExecutionReportPendingCancelMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [PartiesGroups.decode_encode, some_bind]
  rfl

end ExecutionReportPendingCancelMessage

/-- Pending Mass Cancel Message: 55 bytes -/
structure PendingMassCancelMessage where
  sendingTime : BitVec 64
  clordid : Alpha 16
  symbol : Alpha 6
  symbolSfx : Alpha 6
  sideOptional : SideOptional
  lowerThanPrice : BitVec 64
  higherThanPrice : BitVec 64
  cancelGroupId : BitVec 16
  deriving DecidableEq, Repr

namespace PendingMassCancelMessage

def encode (message : PendingMassCancelMessage) : List UInt8 :=
  encodeUInt 8 message.sendingTime
    ++ (Alpha.encode message.clordid
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.symbolSfx
    ++ (SideOptional.encode message.sideOptional
    ++ (encodeUInt 8 message.lowerThanPrice
    ++ (encodeUInt 8 message.higherThanPrice
    ++ (encodeUInt 2 message.cancelGroupId)))))))

def decode (bytes : List UInt8) : Option (PendingMassCancelMessage × List UInt8) := do
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  let (clordid, bytes) ← Alpha.decode 16 bytes
  let (symbol, bytes) ← Alpha.decode 6 bytes
  let (symbolSfx, bytes) ← Alpha.decode 6 bytes
  let (sideOptional, bytes) ← SideOptional.decode bytes
  let (lowerThanPrice, bytes) ← decodeUInt 8 bytes
  let (higherThanPrice, bytes) ← decodeUInt 8 bytes
  let (cancelGroupId, bytes) ← decodeUInt 2 bytes
  pure ({ sendingTime, clordid, symbol, symbolSfx, sideOptional, lowerThanPrice, higherThanPrice, cancelGroupId }, bytes)

@[simp] theorem encode_length (message : PendingMassCancelMessage) : (encode message).length = 55 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, SideOptional.encode_length]

theorem encode_length_pos (message : PendingMassCancelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PendingMassCancelMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SideOptional.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end PendingMassCancelMessage

/-- Execution Report Canceled Message -/
structure ExecutionReportCanceledMessage where
  sendingTime : BitVec 64
  clordid : Alpha 16
  origclordidOptional : Alpha 16
  orderId : BitVec 64
  execId : BitVec 64
  ordStatus : OrdStatus
  leavesQty : BitVec 32
  cumQty : BitVec 32
  cancelReason : BitVec 8
  transactTime : BitVec 64
  linkIdOptional : Alpha 4
  partiesGroups : PartiesGroups
  deriving DecidableEq, Repr

namespace ExecutionReportCanceledMessage

def encode (message : ExecutionReportCanceledMessage) : List UInt8 :=
  encodeUInt 8 message.sendingTime
    ++ (Alpha.encode message.clordid
    ++ (Alpha.encode message.origclordidOptional
    ++ (encodeUInt 8 message.orderId
    ++ (encodeUInt 8 message.execId
    ++ (OrdStatus.encode message.ordStatus
    ++ (encodeUInt 4 message.leavesQty
    ++ (encodeUInt 4 message.cumQty
    ++ (encodeUInt 1 message.cancelReason
    ++ (encodeUInt 8 message.transactTime
    ++ (Alpha.encode message.linkIdOptional
    ++ (PartiesGroups.encode message.partiesGroups)))))))))))

def decode (bytes : List UInt8) : Option (ExecutionReportCanceledMessage × List UInt8) := do
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  let (clordid, bytes) ← Alpha.decode 16 bytes
  let (origclordidOptional, bytes) ← Alpha.decode 16 bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (execId, bytes) ← decodeUInt 8 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (leavesQty, bytes) ← decodeUInt 4 bytes
  let (cumQty, bytes) ← decodeUInt 4 bytes
  let (cancelReason, bytes) ← decodeUInt 1 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (linkIdOptional, bytes) ← Alpha.decode 4 bytes
  let (partiesGroups, bytes) ← PartiesGroups.decode bytes
  pure ({ sendingTime, clordid, origclordidOptional, orderId, execId, ordStatus, leavesQty, cumQty, cancelReason, transactTime, linkIdOptional, partiesGroups }, bytes)

theorem encode_length_pos (message : ExecutionReportCanceledMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ExecutionReportCanceledMessage) : (encode message).length ≤ 4670 := by
  have bound_partiesGroups := PartiesGroups.encode_length_le message.partiesGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OrdStatus.encode_length]
  omega

@[simp] theorem decode_encode (message : ExecutionReportCanceledMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [PartiesGroups.decode_encode, some_bind]
  rfl

end ExecutionReportCanceledMessage

/-- Mass Cancel Done Message: 24 bytes -/
structure MassCancelDoneMessage where
  sendingTime : BitVec 64
  clordid : Alpha 16
  deriving DecidableEq, Repr

namespace MassCancelDoneMessage

def encode (message : MassCancelDoneMessage) : List UInt8 :=
  encodeUInt 8 message.sendingTime
    ++ (Alpha.encode message.clordid)

def decode (bytes : List UInt8) : Option (MassCancelDoneMessage × List UInt8) := do
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  let (clordid, bytes) ← Alpha.decode 16 bytes
  pure ({ sendingTime, clordid }, bytes)

@[simp] theorem encode_length (message : MassCancelDoneMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : MassCancelDoneMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassCancelDoneMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MassCancelDoneMessage

/-- Execution Report Pending Replace Message -/
structure ExecutionReportPendingReplaceMessage where
  sendingTime : BitVec 64
  orderId : BitVec 64
  clordid : Alpha 16
  origclordidOptional : Alpha 16
  execId : BitVec 64
  symbol : Alpha 6
  symbolSfx : Alpha 6
  side : Side
  orderQty : BitVec 32
  ordType : OrdType
  price : BitVec 64
  displayQty : BitVec 32
  locateReqd : Alpha 1
  ordStatus : OrdStatus
  leavesQty : BitVec 32
  cumQty : BitVec 32
  linkIdOptional : Alpha 4
  locateBrokerOptional : Alpha 4
  partiesGroups : PartiesGroups
  deriving DecidableEq, Repr

namespace ExecutionReportPendingReplaceMessage

def encode (message : ExecutionReportPendingReplaceMessage) : List UInt8 :=
  encodeUInt 8 message.sendingTime
    ++ (encodeUInt 8 message.orderId
    ++ (Alpha.encode message.clordid
    ++ (Alpha.encode message.origclordidOptional
    ++ (encodeUInt 8 message.execId
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.symbolSfx
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.orderQty
    ++ (OrdType.encode message.ordType
    ++ (encodeUInt 8 message.price
    ++ (encodeUInt 4 message.displayQty
    ++ (Alpha.encode message.locateReqd
    ++ (OrdStatus.encode message.ordStatus
    ++ (encodeUInt 4 message.leavesQty
    ++ (encodeUInt 4 message.cumQty
    ++ (Alpha.encode message.linkIdOptional
    ++ (Alpha.encode message.locateBrokerOptional
    ++ (PartiesGroups.encode message.partiesGroups))))))))))))))))))

def decode (bytes : List UInt8) : Option (ExecutionReportPendingReplaceMessage × List UInt8) := do
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (clordid, bytes) ← Alpha.decode 16 bytes
  let (origclordidOptional, bytes) ← Alpha.decode 16 bytes
  let (execId, bytes) ← decodeUInt 8 bytes
  let (symbol, bytes) ← Alpha.decode 6 bytes
  let (symbolSfx, bytes) ← Alpha.decode 6 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderQty, bytes) ← decodeUInt 4 bytes
  let (ordType, bytes) ← OrdType.decode bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (displayQty, bytes) ← decodeUInt 4 bytes
  let (locateReqd, bytes) ← Alpha.decode 1 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (leavesQty, bytes) ← decodeUInt 4 bytes
  let (cumQty, bytes) ← decodeUInt 4 bytes
  let (linkIdOptional, bytes) ← Alpha.decode 4 bytes
  let (locateBrokerOptional, bytes) ← Alpha.decode 4 bytes
  let (partiesGroups, bytes) ← PartiesGroups.decode bytes
  pure ({ sendingTime, orderId, clordid, origclordidOptional, execId, symbol, symbolSfx, side, orderQty, ordType, price, displayQty, locateReqd, ordStatus, leavesQty, cumQty, linkIdOptional, locateBrokerOptional, partiesGroups }, bytes)

theorem encode_length_pos (message : ExecutionReportPendingReplaceMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ExecutionReportPendingReplaceMessage) : (encode message).length ≤ 4696 := by
  have bound_partiesGroups := PartiesGroups.encode_length_le message.partiesGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, Side.encode_length, OrdType.encode_length, OrdStatus.encode_length]
  omega

@[simp] theorem decode_encode (message : ExecutionReportPendingReplaceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrdType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [PartiesGroups.decode_encode, some_bind]
  rfl

end ExecutionReportPendingReplaceMessage

/-- Execution Report Replaced Message -/
structure ExecutionReportReplacedMessage where
  sendingTime : BitVec 64
  orderId : BitVec 64
  clordid : Alpha 16
  origclordidOptional : Alpha 16
  execId : BitVec 64
  symbol : Alpha 6
  symbolSfx : Alpha 6
  side : Side
  orderQty : BitVec 32
  ordType : OrdType
  price : BitVec 64
  displayQty : BitVec 32
  locateReqd : Alpha 1
  ordStatus : OrdStatus
  leavesQty : BitVec 32
  cumQty : BitVec 32
  transactTime : BitVec 64
  linkIdOptional : Alpha 4
  locateBrokerOptional : Alpha 4
  partiesGroups : PartiesGroups
  deriving DecidableEq, Repr

namespace ExecutionReportReplacedMessage

def encode (message : ExecutionReportReplacedMessage) : List UInt8 :=
  encodeUInt 8 message.sendingTime
    ++ (encodeUInt 8 message.orderId
    ++ (Alpha.encode message.clordid
    ++ (Alpha.encode message.origclordidOptional
    ++ (encodeUInt 8 message.execId
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.symbolSfx
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.orderQty
    ++ (OrdType.encode message.ordType
    ++ (encodeUInt 8 message.price
    ++ (encodeUInt 4 message.displayQty
    ++ (Alpha.encode message.locateReqd
    ++ (OrdStatus.encode message.ordStatus
    ++ (encodeUInt 4 message.leavesQty
    ++ (encodeUInt 4 message.cumQty
    ++ (encodeUInt 8 message.transactTime
    ++ (Alpha.encode message.linkIdOptional
    ++ (Alpha.encode message.locateBrokerOptional
    ++ (PartiesGroups.encode message.partiesGroups)))))))))))))))))))

def decode (bytes : List UInt8) : Option (ExecutionReportReplacedMessage × List UInt8) := do
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (clordid, bytes) ← Alpha.decode 16 bytes
  let (origclordidOptional, bytes) ← Alpha.decode 16 bytes
  let (execId, bytes) ← decodeUInt 8 bytes
  let (symbol, bytes) ← Alpha.decode 6 bytes
  let (symbolSfx, bytes) ← Alpha.decode 6 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderQty, bytes) ← decodeUInt 4 bytes
  let (ordType, bytes) ← OrdType.decode bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (displayQty, bytes) ← decodeUInt 4 bytes
  let (locateReqd, bytes) ← Alpha.decode 1 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (leavesQty, bytes) ← decodeUInt 4 bytes
  let (cumQty, bytes) ← decodeUInt 4 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (linkIdOptional, bytes) ← Alpha.decode 4 bytes
  let (locateBrokerOptional, bytes) ← Alpha.decode 4 bytes
  let (partiesGroups, bytes) ← PartiesGroups.decode bytes
  pure ({ sendingTime, orderId, clordid, origclordidOptional, execId, symbol, symbolSfx, side, orderQty, ordType, price, displayQty, locateReqd, ordStatus, leavesQty, cumQty, transactTime, linkIdOptional, locateBrokerOptional, partiesGroups }, bytes)

theorem encode_length_pos (message : ExecutionReportReplacedMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ExecutionReportReplacedMessage) : (encode message).length ≤ 4704 := by
  have bound_partiesGroups := PartiesGroups.encode_length_le message.partiesGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, Side.encode_length, OrdType.encode_length, OrdStatus.encode_length]
  omega

@[simp] theorem decode_encode (message : ExecutionReportReplacedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrdType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [PartiesGroups.decode_encode, some_bind]
  rfl

end ExecutionReportReplacedMessage

/-- Execution Report Trade Correction Message -/
structure ExecutionReportTradeCorrectionMessage where
  sendingTime : BitVec 64
  orderId : BitVec 64
  clordid : Alpha 16
  execId : BitVec 64
  execRefId : BitVec 64
  trdMatchId : BitVec 64
  ordStatus : OrdStatus
  lastPx : BitVec 64
  lastQtyOptional : BitVec 32
  leavesQty : BitVec 32
  cumQty : BitVec 32
  linkIdOptional : Alpha 4
  securityGroup : Alpha 1
  partiesGroups : PartiesGroups
  deriving DecidableEq, Repr

namespace ExecutionReportTradeCorrectionMessage

def encode (message : ExecutionReportTradeCorrectionMessage) : List UInt8 :=
  encodeUInt 8 message.sendingTime
    ++ (encodeUInt 8 message.orderId
    ++ (Alpha.encode message.clordid
    ++ (encodeUInt 8 message.execId
    ++ (encodeUInt 8 message.execRefId
    ++ (encodeUInt 8 message.trdMatchId
    ++ (OrdStatus.encode message.ordStatus
    ++ (encodeUInt 8 message.lastPx
    ++ (encodeUInt 4 message.lastQtyOptional
    ++ (encodeUInt 4 message.leavesQty
    ++ (encodeUInt 4 message.cumQty
    ++ (Alpha.encode message.linkIdOptional
    ++ (Alpha.encode message.securityGroup
    ++ (PartiesGroups.encode message.partiesGroups)))))))))))))

def decode (bytes : List UInt8) : Option (ExecutionReportTradeCorrectionMessage × List UInt8) := do
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (clordid, bytes) ← Alpha.decode 16 bytes
  let (execId, bytes) ← decodeUInt 8 bytes
  let (execRefId, bytes) ← decodeUInt 8 bytes
  let (trdMatchId, bytes) ← decodeUInt 8 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (lastPx, bytes) ← decodeUInt 8 bytes
  let (lastQtyOptional, bytes) ← decodeUInt 4 bytes
  let (leavesQty, bytes) ← decodeUInt 4 bytes
  let (cumQty, bytes) ← decodeUInt 4 bytes
  let (linkIdOptional, bytes) ← Alpha.decode 4 bytes
  let (securityGroup, bytes) ← Alpha.decode 1 bytes
  let (partiesGroups, bytes) ← PartiesGroups.decode bytes
  pure ({ sendingTime, orderId, clordid, execId, execRefId, trdMatchId, ordStatus, lastPx, lastQtyOptional, leavesQty, cumQty, linkIdOptional, securityGroup, partiesGroups }, bytes)

theorem encode_length_pos (message : ExecutionReportTradeCorrectionMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ExecutionReportTradeCorrectionMessage) : (encode message).length ≤ 4674 := by
  have bound_partiesGroups := PartiesGroups.encode_length_le message.partiesGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OrdStatus.encode_length]
  omega

@[simp] theorem decode_encode (message : ExecutionReportTradeCorrectionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [PartiesGroups.decode_encode, some_bind]
  rfl

end ExecutionReportTradeCorrectionMessage

/-- Execution Report Trade Break Message -/
structure ExecutionReportTradeBreakMessage where
  sendingTime : BitVec 64
  orderId : BitVec 64
  clordid : Alpha 16
  execId : BitVec 64
  execRefId : BitVec 64
  trdMatchId : BitVec 64
  ordStatus : OrdStatus
  leavesQty : BitVec 32
  cumQty : BitVec 32
  linkIdOptional : Alpha 4
  securityGroup : Alpha 1
  partiesGroups : PartiesGroups
  deriving DecidableEq, Repr

namespace ExecutionReportTradeBreakMessage

def encode (message : ExecutionReportTradeBreakMessage) : List UInt8 :=
  encodeUInt 8 message.sendingTime
    ++ (encodeUInt 8 message.orderId
    ++ (Alpha.encode message.clordid
    ++ (encodeUInt 8 message.execId
    ++ (encodeUInt 8 message.execRefId
    ++ (encodeUInt 8 message.trdMatchId
    ++ (OrdStatus.encode message.ordStatus
    ++ (encodeUInt 4 message.leavesQty
    ++ (encodeUInt 4 message.cumQty
    ++ (Alpha.encode message.linkIdOptional
    ++ (Alpha.encode message.securityGroup
    ++ (PartiesGroups.encode message.partiesGroups)))))))))))

def decode (bytes : List UInt8) : Option (ExecutionReportTradeBreakMessage × List UInt8) := do
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (clordid, bytes) ← Alpha.decode 16 bytes
  let (execId, bytes) ← decodeUInt 8 bytes
  let (execRefId, bytes) ← decodeUInt 8 bytes
  let (trdMatchId, bytes) ← decodeUInt 8 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (leavesQty, bytes) ← decodeUInt 4 bytes
  let (cumQty, bytes) ← decodeUInt 4 bytes
  let (linkIdOptional, bytes) ← Alpha.decode 4 bytes
  let (securityGroup, bytes) ← Alpha.decode 1 bytes
  let (partiesGroups, bytes) ← PartiesGroups.decode bytes
  pure ({ sendingTime, orderId, clordid, execId, execRefId, trdMatchId, ordStatus, leavesQty, cumQty, linkIdOptional, securityGroup, partiesGroups }, bytes)

theorem encode_length_pos (message : ExecutionReportTradeBreakMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ExecutionReportTradeBreakMessage) : (encode message).length ≤ 4662 := by
  have bound_partiesGroups := PartiesGroups.encode_length_le message.partiesGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OrdStatus.encode_length]
  omega

@[simp] theorem decode_encode (message : ExecutionReportTradeBreakMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [PartiesGroups.decode_encode, some_bind]
  rfl

end ExecutionReportTradeBreakMessage

/-- Execution Report Restatement Message -/
structure ExecutionReportRestatementMessage where
  sendingTime : BitVec 64
  orderId : BitVec 64
  clordid : Alpha 16
  execId : BitVec 64
  ordStatus : OrdStatus
  lastPxOptional : BitVec 64
  leavesQty : BitVec 32
  cumQty : BitVec 32
  lastShares : BitVec 32
  execRestatementReason : BitVec 8
  transactTime : BitVec 64
  extendedRestatementReason : BitVec 8
  linkIdOptional : Alpha 4
  partiesGroups : PartiesGroups
  deriving DecidableEq, Repr

namespace ExecutionReportRestatementMessage

def encode (message : ExecutionReportRestatementMessage) : List UInt8 :=
  encodeUInt 8 message.sendingTime
    ++ (encodeUInt 8 message.orderId
    ++ (Alpha.encode message.clordid
    ++ (encodeUInt 8 message.execId
    ++ (OrdStatus.encode message.ordStatus
    ++ (encodeUInt 8 message.lastPxOptional
    ++ (encodeUInt 4 message.leavesQty
    ++ (encodeUInt 4 message.cumQty
    ++ (encodeUInt 4 message.lastShares
    ++ (encodeUInt 1 message.execRestatementReason
    ++ (encodeUInt 8 message.transactTime
    ++ (encodeUInt 1 message.extendedRestatementReason
    ++ (Alpha.encode message.linkIdOptional
    ++ (PartiesGroups.encode message.partiesGroups)))))))))))))

def decode (bytes : List UInt8) : Option (ExecutionReportRestatementMessage × List UInt8) := do
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (clordid, bytes) ← Alpha.decode 16 bytes
  let (execId, bytes) ← decodeUInt 8 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (lastPxOptional, bytes) ← decodeUInt 8 bytes
  let (leavesQty, bytes) ← decodeUInt 4 bytes
  let (cumQty, bytes) ← decodeUInt 4 bytes
  let (lastShares, bytes) ← decodeUInt 4 bytes
  let (execRestatementReason, bytes) ← decodeUInt 1 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (extendedRestatementReason, bytes) ← decodeUInt 1 bytes
  let (linkIdOptional, bytes) ← Alpha.decode 4 bytes
  let (partiesGroups, bytes) ← PartiesGroups.decode bytes
  pure ({ sendingTime, orderId, clordid, execId, ordStatus, lastPxOptional, leavesQty, cumQty, lastShares, execRestatementReason, transactTime, extendedRestatementReason, linkIdOptional, partiesGroups }, bytes)

theorem encode_length_pos (message : ExecutionReportRestatementMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ExecutionReportRestatementMessage) : (encode message).length ≤ 4667 := by
  have bound_partiesGroups := PartiesGroups.encode_length_le message.partiesGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OrdStatus.encode_length]
  omega

@[simp] theorem decode_encode (message : ExecutionReportRestatementMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [PartiesGroups.decode_encode, some_bind]
  rfl

end ExecutionReportRestatementMessage

/-- Order Cancel Reject Message: 30 bytes -/
structure OrderCancelRejectMessage where
  sendingTime : BitVec 64
  clordid : Alpha 16
  cxlRejResponseTo : CxlRejResponseTo
  cxlRejReason : BitVec 8
  linkIdOptional : Alpha 4
  deriving DecidableEq, Repr

namespace OrderCancelRejectMessage

def encode (message : OrderCancelRejectMessage) : List UInt8 :=
  encodeUInt 8 message.sendingTime
    ++ (Alpha.encode message.clordid
    ++ (CxlRejResponseTo.encode message.cxlRejResponseTo
    ++ (encodeUInt 1 message.cxlRejReason
    ++ (Alpha.encode message.linkIdOptional))))

def decode (bytes : List UInt8) : Option (OrderCancelRejectMessage × List UInt8) := do
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  let (clordid, bytes) ← Alpha.decode 16 bytes
  let (cxlRejResponseTo, bytes) ← CxlRejResponseTo.decode bytes
  let (cxlRejReason, bytes) ← decodeUInt 1 bytes
  let (linkIdOptional, bytes) ← Alpha.decode 4 bytes
  pure ({ sendingTime, clordid, cxlRejResponseTo, cxlRejReason, linkIdOptional }, bytes)

@[simp] theorem encode_length (message : OrderCancelRejectMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, CxlRejResponseTo.encode_length]

theorem encode_length_pos (message : OrderCancelRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancelRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CxlRejResponseTo.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderCancelRejectMessage

/-- Mass Cancel Reject Message: 56 bytes -/
structure MassCancelRejectMessage where
  sendingTime : BitVec 64
  clordid : Alpha 16
  symbol : Alpha 6
  symbolSfx : Alpha 6
  sideOptional : SideOptional
  lowerThanPrice : BitVec 64
  higherThanPrice : BitVec 64
  cancelGroupId : BitVec 16
  massCancelRejectReason : BitVec 8
  deriving DecidableEq, Repr

namespace MassCancelRejectMessage

def encode (message : MassCancelRejectMessage) : List UInt8 :=
  encodeUInt 8 message.sendingTime
    ++ (Alpha.encode message.clordid
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.symbolSfx
    ++ (SideOptional.encode message.sideOptional
    ++ (encodeUInt 8 message.lowerThanPrice
    ++ (encodeUInt 8 message.higherThanPrice
    ++ (encodeUInt 2 message.cancelGroupId
    ++ (encodeUInt 1 message.massCancelRejectReason))))))))

def decode (bytes : List UInt8) : Option (MassCancelRejectMessage × List UInt8) := do
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  let (clordid, bytes) ← Alpha.decode 16 bytes
  let (symbol, bytes) ← Alpha.decode 6 bytes
  let (symbolSfx, bytes) ← Alpha.decode 6 bytes
  let (sideOptional, bytes) ← SideOptional.decode bytes
  let (lowerThanPrice, bytes) ← decodeUInt 8 bytes
  let (higherThanPrice, bytes) ← decodeUInt 8 bytes
  let (cancelGroupId, bytes) ← decodeUInt 2 bytes
  let (massCancelRejectReason, bytes) ← decodeUInt 1 bytes
  pure ({ sendingTime, clordid, symbol, symbolSfx, sideOptional, lowerThanPrice, higherThanPrice, cancelGroupId, massCancelRejectReason }, bytes)

@[simp] theorem encode_length (message : MassCancelRejectMessage) : (encode message).length = 56 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, SideOptional.encode_length]

theorem encode_length_pos (message : MassCancelRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassCancelRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SideOptional.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MassCancelRejectMessage

/-- Any Payload, selected by Template Id -/
inductive Payload where
  | newOrderSingleMessage (message : NewOrderSingleMessage) -- 1
  | orderCancelReplaceRequestMessage (message : OrderCancelReplaceRequestMessage) -- 2
  | orderCancelRequestMessage (message : OrderCancelRequestMessage) -- 3
  | massCancelRequestMessage (message : MassCancelRequestMessage) -- 4
  | executionReportPendingNewMessage (message : ExecutionReportPendingNewMessage) -- 5
  | executionReportNewMessage (message : ExecutionReportNewMessage) -- 6
  | executionReportRejectedMessage (message : ExecutionReportRejectedMessage) -- 7
  | executionReportTradeMessage (message : ExecutionReportTradeMessage) -- 8
  | executionReportPendingCancelMessage (message : ExecutionReportPendingCancelMessage) -- 9
  | pendingMassCancelMessage (message : PendingMassCancelMessage) -- 10
  | executionReportCanceledMessage (message : ExecutionReportCanceledMessage) -- 11
  | massCancelDoneMessage (message : MassCancelDoneMessage) -- 12
  | executionReportPendingReplaceMessage (message : ExecutionReportPendingReplaceMessage) -- 13
  | executionReportReplacedMessage (message : ExecutionReportReplacedMessage) -- 14
  | executionReportTradeCorrectionMessage (message : ExecutionReportTradeCorrectionMessage) -- 15
  | executionReportTradeBreakMessage (message : ExecutionReportTradeBreakMessage) -- 16
  | executionReportRestatementMessage (message : ExecutionReportRestatementMessage) -- 17
  | orderCancelRejectMessage (message : OrderCancelRejectMessage) -- 18
  | massCancelRejectMessage (message : MassCancelRejectMessage) -- 20
  deriving DecidableEq, Repr

namespace Payload

/-- The Template Id each message is sent under -/
def tag : Payload → BitVec 8
  | .newOrderSingleMessage _ => 1
  | .orderCancelReplaceRequestMessage _ => 2
  | .orderCancelRequestMessage _ => 3
  | .massCancelRequestMessage _ => 4
  | .executionReportPendingNewMessage _ => 5
  | .executionReportNewMessage _ => 6
  | .executionReportRejectedMessage _ => 7
  | .executionReportTradeMessage _ => 8
  | .executionReportPendingCancelMessage _ => 9
  | .pendingMassCancelMessage _ => 10
  | .executionReportCanceledMessage _ => 11
  | .massCancelDoneMessage _ => 12
  | .executionReportPendingReplaceMessage _ => 13
  | .executionReportReplacedMessage _ => 14
  | .executionReportTradeCorrectionMessage _ => 15
  | .executionReportTradeBreakMessage _ => 16
  | .executionReportRestatementMessage _ => 17
  | .orderCancelRejectMessage _ => 18
  | .massCancelRejectMessage _ => 20

def encode : Payload → List UInt8
  | .newOrderSingleMessage message => NewOrderSingleMessage.encode message
  | .orderCancelReplaceRequestMessage message => OrderCancelReplaceRequestMessage.encode message
  | .orderCancelRequestMessage message => OrderCancelRequestMessage.encode message
  | .massCancelRequestMessage message => MassCancelRequestMessage.encode message
  | .executionReportPendingNewMessage message => ExecutionReportPendingNewMessage.encode message
  | .executionReportNewMessage message => ExecutionReportNewMessage.encode message
  | .executionReportRejectedMessage message => ExecutionReportRejectedMessage.encode message
  | .executionReportTradeMessage message => ExecutionReportTradeMessage.encode message
  | .executionReportPendingCancelMessage message => ExecutionReportPendingCancelMessage.encode message
  | .pendingMassCancelMessage message => PendingMassCancelMessage.encode message
  | .executionReportCanceledMessage message => ExecutionReportCanceledMessage.encode message
  | .massCancelDoneMessage message => MassCancelDoneMessage.encode message
  | .executionReportPendingReplaceMessage message => ExecutionReportPendingReplaceMessage.encode message
  | .executionReportReplacedMessage message => ExecutionReportReplacedMessage.encode message
  | .executionReportTradeCorrectionMessage message => ExecutionReportTradeCorrectionMessage.encode message
  | .executionReportTradeBreakMessage message => ExecutionReportTradeBreakMessage.encode message
  | .executionReportRestatementMessage message => ExecutionReportRestatementMessage.encode message
  | .orderCancelRejectMessage message => OrderCancelRejectMessage.encode message
  | .massCancelRejectMessage message => MassCancelRejectMessage.encode message

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 1 then (NewOrderSingleMessage.decode bytes).map fun (message, rest) => (.newOrderSingleMessage message, rest)
  else if tag = 2 then (OrderCancelReplaceRequestMessage.decode bytes).map fun (message, rest) => (.orderCancelReplaceRequestMessage message, rest)
  else if tag = 3 then (OrderCancelRequestMessage.decode bytes).map fun (message, rest) => (.orderCancelRequestMessage message, rest)
  else if tag = 4 then (MassCancelRequestMessage.decode bytes).map fun (message, rest) => (.massCancelRequestMessage message, rest)
  else if tag = 5 then (ExecutionReportPendingNewMessage.decode bytes).map fun (message, rest) => (.executionReportPendingNewMessage message, rest)
  else if tag = 6 then (ExecutionReportNewMessage.decode bytes).map fun (message, rest) => (.executionReportNewMessage message, rest)
  else if tag = 7 then (ExecutionReportRejectedMessage.decode bytes).map fun (message, rest) => (.executionReportRejectedMessage message, rest)
  else if tag = 8 then (ExecutionReportTradeMessage.decode bytes).map fun (message, rest) => (.executionReportTradeMessage message, rest)
  else if tag = 9 then (ExecutionReportPendingCancelMessage.decode bytes).map fun (message, rest) => (.executionReportPendingCancelMessage message, rest)
  else if tag = 10 then (PendingMassCancelMessage.decode bytes).map fun (message, rest) => (.pendingMassCancelMessage message, rest)
  else if tag = 11 then (ExecutionReportCanceledMessage.decode bytes).map fun (message, rest) => (.executionReportCanceledMessage message, rest)
  else if tag = 12 then (MassCancelDoneMessage.decode bytes).map fun (message, rest) => (.massCancelDoneMessage message, rest)
  else if tag = 13 then (ExecutionReportPendingReplaceMessage.decode bytes).map fun (message, rest) => (.executionReportPendingReplaceMessage message, rest)
  else if tag = 14 then (ExecutionReportReplacedMessage.decode bytes).map fun (message, rest) => (.executionReportReplacedMessage message, rest)
  else if tag = 15 then (ExecutionReportTradeCorrectionMessage.decode bytes).map fun (message, rest) => (.executionReportTradeCorrectionMessage message, rest)
  else if tag = 16 then (ExecutionReportTradeBreakMessage.decode bytes).map fun (message, rest) => (.executionReportTradeBreakMessage message, rest)
  else if tag = 17 then (ExecutionReportRestatementMessage.decode bytes).map fun (message, rest) => (.executionReportRestatementMessage message, rest)
  else if tag = 18 then (OrderCancelRejectMessage.decode bytes).map fun (message, rest) => (.orderCancelRejectMessage message, rest)
  else if tag = 20 then (MassCancelRejectMessage.decode bytes).map fun (message, rest) => (.massCancelRejectMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Sbe Message -/
structure SbeMessage where
  blockLength : BitVec 16
  schemaId : BitVec 8
  version : BitVec 16
  payload : Payload
  deriving DecidableEq, Repr

namespace SbeMessage

def encode (message : SbeMessage) : List UInt8 :=
  encodeUInt 2 message.blockLength
    ++ (encodeUInt 1 (Payload.tag message.payload)
    ++ (encodeUInt 1 message.schemaId
    ++ (encodeUInt 2 message.version
    ++ (Payload.encode message.payload))))

def decode (bytes : List UInt8) : Option (SbeMessage × List UInt8) := do
  let (blockLength, bytes) ← decodeUInt 2 bytes
  let (templateId, bytes) ← decodeUInt 1 bytes
  let (schemaId, bytes) ← decodeUInt 1 bytes
  let (version, bytes) ← decodeUInt 2 bytes
  let (payload, bytes) ← Payload.decode templateId bytes
  pure ({ blockLength, schemaId, version, payload }, bytes)

theorem encode_length_pos (message : SbeMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SbeMessage) : (encode message).length ≤ 4735 := by
  unfold encode
  cases message.payload with
  | newOrderSingleMessage inner =>
    have bound_inner := NewOrderSingleMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega
  | orderCancelReplaceRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, OrderCancelReplaceRequestMessage.encode_length]
    omega
  | orderCancelRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, OrderCancelRequestMessage.encode_length]
    omega
  | massCancelRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MassCancelRequestMessage.encode_length]
    omega
  | executionReportPendingNewMessage inner =>
    have bound_inner := ExecutionReportPendingNewMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega
  | executionReportNewMessage inner =>
    have bound_inner := ExecutionReportNewMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega
  | executionReportRejectedMessage inner =>
    have bound_inner := ExecutionReportRejectedMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega
  | executionReportTradeMessage inner =>
    have bound_inner := ExecutionReportTradeMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega
  | executionReportPendingCancelMessage inner =>
    have bound_inner := ExecutionReportPendingCancelMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega
  | pendingMassCancelMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, PendingMassCancelMessage.encode_length]
    omega
  | executionReportCanceledMessage inner =>
    have bound_inner := ExecutionReportCanceledMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega
  | massCancelDoneMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MassCancelDoneMessage.encode_length]
    omega
  | executionReportPendingReplaceMessage inner =>
    have bound_inner := ExecutionReportPendingReplaceMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega
  | executionReportReplacedMessage inner =>
    have bound_inner := ExecutionReportReplacedMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega
  | executionReportTradeCorrectionMessage inner =>
    have bound_inner := ExecutionReportTradeCorrectionMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega
  | executionReportTradeBreakMessage inner =>
    have bound_inner := ExecutionReportTradeBreakMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega
  | executionReportRestatementMessage inner =>
    have bound_inner := ExecutionReportRestatementMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega
  | orderCancelRejectMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, OrderCancelRejectMessage.encode_length]
    omega
  | massCancelRejectMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MassCancelRejectMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : SbeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

end SbeMessage

/-- Unsequenced Message -/
structure UnsequencedMessage where
  sbeMessage : SbeMessage
  deriving DecidableEq, Repr

namespace UnsequencedMessage

def encode (message : UnsequencedMessage) : List UInt8 :=
  SbeMessage.encode message.sbeMessage

def decode (bytes : List UInt8) : Option (UnsequencedMessage × List UInt8) := do
  let (sbeMessage, bytes) ← SbeMessage.decode bytes
  pure ({ sbeMessage }, bytes)

theorem encode_length_pos (message : UnsequencedMessage) : (encode message).length > 0 := by
  have positive := SbeMessage.encode_length_pos message.sbeMessage
  unfold encode
  omega

@[simp] theorem decode_encode (message : UnsequencedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [SbeMessage.decode_encode, some_bind]
  rfl

end UnsequencedMessage

/-- Login Accepted Message: 1 bytes -/
structure LoginAcceptedMessage where
  supportedRequestMode : SupportedRequestMode
  deriving DecidableEq, Repr

namespace LoginAcceptedMessage

def encode (message : LoginAcceptedMessage) : List UInt8 :=
  SupportedRequestMode.encode message.supportedRequestMode

def decode (bytes : List UInt8) : Option (LoginAcceptedMessage × List UInt8) := do
  let (supportedRequestMode, bytes) ← SupportedRequestMode.decode bytes
  pure ({ supportedRequestMode }, bytes)

@[simp] theorem encode_length (message : LoginAcceptedMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [SupportedRequestMode.encode_length]

theorem encode_length_pos (message : LoginAcceptedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginAcceptedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [SupportedRequestMode.decode_encode, some_bind]
  rfl

end LoginAcceptedMessage

/-- Login Rejected Message: 1 bytes -/
structure LoginRejectedMessage where
  loginRejectCode : LoginRejectCode
  deriving DecidableEq, Repr

namespace LoginRejectedMessage

def encode (message : LoginRejectedMessage) : List UInt8 :=
  LoginRejectCode.encode message.loginRejectCode

def decode (bytes : List UInt8) : Option (LoginRejectedMessage × List UInt8) := do
  let (loginRejectCode, bytes) ← LoginRejectCode.decode bytes
  pure ({ loginRejectCode }, bytes)

@[simp] theorem encode_length (message : LoginRejectedMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [LoginRejectCode.encode_length]

theorem encode_length_pos (message : LoginRejectedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRejectedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [LoginRejectCode.decode_encode, some_bind]
  rfl

end LoginRejectedMessage

/-- Start Of Session Message: 8 bytes -/
structure StartOfSessionMessage where
  sessionId : BitVec 64
  deriving DecidableEq, Repr

namespace StartOfSessionMessage

def encode (message : StartOfSessionMessage) : List UInt8 :=
  encodeUInt 8 message.sessionId

def decode (bytes : List UInt8) : Option (StartOfSessionMessage × List UInt8) := do
  let (sessionId, bytes) ← decodeUInt 8 bytes
  pure ({ sessionId }, bytes)

@[simp] theorem encode_length (message : StartOfSessionMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : StartOfSessionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StartOfSessionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end StartOfSessionMessage

/-- Replay Begin Message: 12 bytes -/
structure ReplayBeginMessage where
  nextSequenceNumber : BitVec 64
  pendingMessageCount : BitVec 32
  deriving DecidableEq, Repr

namespace ReplayBeginMessage

def encode (message : ReplayBeginMessage) : List UInt8 :=
  encodeUInt 8 message.nextSequenceNumber
    ++ (encodeUInt 4 message.pendingMessageCount)

def decode (bytes : List UInt8) : Option (ReplayBeginMessage × List UInt8) := do
  let (nextSequenceNumber, bytes) ← decodeUInt 8 bytes
  let (pendingMessageCount, bytes) ← decodeUInt 4 bytes
  pure ({ nextSequenceNumber, pendingMessageCount }, bytes)

@[simp] theorem encode_length (message : ReplayBeginMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : ReplayBeginMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReplayBeginMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ReplayBeginMessage

/-- Replay Rejected Message: 1 bytes -/
structure ReplayRejectedMessage where
  replayRejectCode : ReplayRejectCode
  deriving DecidableEq, Repr

namespace ReplayRejectedMessage

def encode (message : ReplayRejectedMessage) : List UInt8 :=
  ReplayRejectCode.encode message.replayRejectCode

def decode (bytes : List UInt8) : Option (ReplayRejectedMessage × List UInt8) := do
  let (replayRejectCode, bytes) ← ReplayRejectCode.decode bytes
  pure ({ replayRejectCode }, bytes)

@[simp] theorem encode_length (message : ReplayRejectedMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [ReplayRejectCode.encode_length]

theorem encode_length_pos (message : ReplayRejectedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReplayRejectedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [ReplayRejectCode.decode_encode, some_bind]
  rfl

end ReplayRejectedMessage

/-- Replay Complete Message: 8 bytes -/
structure ReplayCompleteMessage where
  messageCount : BitVec 64
  deriving DecidableEq, Repr

namespace ReplayCompleteMessage

def encode (message : ReplayCompleteMessage) : List UInt8 :=
  encodeUInt 8 message.messageCount

def decode (bytes : List UInt8) : Option (ReplayCompleteMessage × List UInt8) := do
  let (messageCount, bytes) ← decodeUInt 8 bytes
  pure ({ messageCount }, bytes)

@[simp] theorem encode_length (message : ReplayCompleteMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : ReplayCompleteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReplayCompleteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ReplayCompleteMessage

/-- Stream Begin Message: 16 bytes -/
structure StreamBeginMessage where
  nextSequenceNumber : BitVec 64
  maxSequenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace StreamBeginMessage

def encode (message : StreamBeginMessage) : List UInt8 :=
  encodeUInt 8 message.nextSequenceNumber
    ++ (encodeUInt 8 message.maxSequenceNumber)

def decode (bytes : List UInt8) : Option (StreamBeginMessage × List UInt8) := do
  let (nextSequenceNumber, bytes) ← decodeUInt 8 bytes
  let (maxSequenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ nextSequenceNumber, maxSequenceNumber }, bytes)

@[simp] theorem encode_length (message : StreamBeginMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : StreamBeginMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StreamBeginMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end StreamBeginMessage

/-- Stream Rejected Message: 1 bytes -/
structure StreamRejectedMessage where
  streamRejectCode : StreamRejectCode
  deriving DecidableEq, Repr

namespace StreamRejectedMessage

def encode (message : StreamRejectedMessage) : List UInt8 :=
  StreamRejectCode.encode message.streamRejectCode

def decode (bytes : List UInt8) : Option (StreamRejectedMessage × List UInt8) := do
  let (streamRejectCode, bytes) ← StreamRejectCode.decode bytes
  pure ({ streamRejectCode }, bytes)

@[simp] theorem encode_length (message : StreamRejectedMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [StreamRejectCode.encode_length]

theorem encode_length_pos (message : StreamRejectedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StreamRejectedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [StreamRejectCode.decode_encode, some_bind]
  rfl

end StreamRejectedMessage

/-- Stream Complete Message: 8 bytes -/
structure StreamCompleteMessage where
  totalSequenceCount : BitVec 64
  deriving DecidableEq, Repr

namespace StreamCompleteMessage

def encode (message : StreamCompleteMessage) : List UInt8 :=
  encodeUInt 8 message.totalSequenceCount

def decode (bytes : List UInt8) : Option (StreamCompleteMessage × List UInt8) := do
  let (totalSequenceCount, bytes) ← decodeUInt 8 bytes
  pure ({ totalSequenceCount }, bytes)

@[simp] theorem encode_length (message : StreamCompleteMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : StreamCompleteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StreamCompleteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end StreamCompleteMessage

/-- Sequenced Message -/
structure SequencedMessage where
  sbeMessage : SbeMessage
  deriving DecidableEq, Repr

namespace SequencedMessage

def encode (message : SequencedMessage) : List UInt8 :=
  SbeMessage.encode message.sbeMessage

def decode (bytes : List UInt8) : Option (SequencedMessage × List UInt8) := do
  let (sbeMessage, bytes) ← SbeMessage.decode bytes
  pure ({ sbeMessage }, bytes)

theorem encode_length_pos (message : SequencedMessage) : (encode message).length > 0 := by
  have positive := SbeMessage.encode_length_pos message.sbeMessage
  unfold encode
  omega

@[simp] theorem decode_encode (message : SequencedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [SbeMessage.decode_encode, some_bind]
  rfl

end SequencedMessage

/-- Any Data, selected by Message Type -/
inductive Data where
  | loginRequestMessage (message : LoginRequestMessage) -- 100
  | replayRequestMessage (message : ReplayRequestMessage) -- 101
  | replayAllRequestMessage (message : ReplayAllRequestMessage) -- 102
  | streamRequestMessage (message : StreamRequestMessage) -- 103
  | unsequencedMessage (message : UnsequencedMessage) -- 104
  | loginAcceptedMessage (message : LoginAcceptedMessage) -- 1
  | loginRejectedMessage (message : LoginRejectedMessage) -- 2
  | startOfSessionMessage (message : StartOfSessionMessage) -- 3
  | replayBeginMessage (message : ReplayBeginMessage) -- 5
  | replayRejectedMessage (message : ReplayRejectedMessage) -- 6
  | replayCompleteMessage (message : ReplayCompleteMessage) -- 7
  | streamBeginMessage (message : StreamBeginMessage) -- 8
  | streamRejectedMessage (message : StreamRejectedMessage) -- 9
  | streamCompleteMessage (message : StreamCompleteMessage) -- 10
  | sequencedMessage (message : SequencedMessage) -- 11
  deriving DecidableEq, Repr

namespace Data

/-- The Message Type each message is sent under -/
def tag : Data → BitVec 8
  | .loginRequestMessage _ => 100
  | .replayRequestMessage _ => 101
  | .replayAllRequestMessage _ => 102
  | .streamRequestMessage _ => 103
  | .unsequencedMessage _ => 104
  | .loginAcceptedMessage _ => 1
  | .loginRejectedMessage _ => 2
  | .startOfSessionMessage _ => 3
  | .replayBeginMessage _ => 5
  | .replayRejectedMessage _ => 6
  | .replayCompleteMessage _ => 7
  | .streamBeginMessage _ => 8
  | .streamRejectedMessage _ => 9
  | .streamCompleteMessage _ => 10
  | .sequencedMessage _ => 11

def encode : Data → List UInt8
  | .loginRequestMessage message => LoginRequestMessage.encode message
  | .replayRequestMessage message => ReplayRequestMessage.encode message
  | .replayAllRequestMessage message => ReplayAllRequestMessage.encode message
  | .streamRequestMessage message => StreamRequestMessage.encode message
  | .unsequencedMessage message => UnsequencedMessage.encode message
  | .loginAcceptedMessage message => LoginAcceptedMessage.encode message
  | .loginRejectedMessage message => LoginRejectedMessage.encode message
  | .startOfSessionMessage message => StartOfSessionMessage.encode message
  | .replayBeginMessage message => ReplayBeginMessage.encode message
  | .replayRejectedMessage message => ReplayRejectedMessage.encode message
  | .replayCompleteMessage message => ReplayCompleteMessage.encode message
  | .streamBeginMessage message => StreamBeginMessage.encode message
  | .streamRejectedMessage message => StreamRejectedMessage.encode message
  | .streamCompleteMessage message => StreamCompleteMessage.encode message
  | .sequencedMessage message => SequencedMessage.encode message

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Data × List UInt8) :=
  if tag = 100 then (LoginRequestMessage.decode bytes).map fun (message, rest) => (.loginRequestMessage message, rest)
  else if tag = 101 then (ReplayRequestMessage.decode bytes).map fun (message, rest) => (.replayRequestMessage message, rest)
  else if tag = 102 then (ReplayAllRequestMessage.decode bytes).map fun (message, rest) => (.replayAllRequestMessage message, rest)
  else if tag = 103 then (StreamRequestMessage.decode bytes).map fun (message, rest) => (.streamRequestMessage message, rest)
  else if tag = 104 then (UnsequencedMessage.decode bytes).map fun (message, rest) => (.unsequencedMessage message, rest)
  else if tag = 1 then (LoginAcceptedMessage.decode bytes).map fun (message, rest) => (.loginAcceptedMessage message, rest)
  else if tag = 2 then (LoginRejectedMessage.decode bytes).map fun (message, rest) => (.loginRejectedMessage message, rest)
  else if tag = 3 then (StartOfSessionMessage.decode bytes).map fun (message, rest) => (.startOfSessionMessage message, rest)
  else if tag = 5 then (ReplayBeginMessage.decode bytes).map fun (message, rest) => (.replayBeginMessage message, rest)
  else if tag = 6 then (ReplayRejectedMessage.decode bytes).map fun (message, rest) => (.replayRejectedMessage message, rest)
  else if tag = 7 then (ReplayCompleteMessage.decode bytes).map fun (message, rest) => (.replayCompleteMessage message, rest)
  else if tag = 8 then (StreamBeginMessage.decode bytes).map fun (message, rest) => (.streamBeginMessage message, rest)
  else if tag = 9 then (StreamRejectedMessage.decode bytes).map fun (message, rest) => (.streamRejectedMessage message, rest)
  else if tag = 10 then (StreamCompleteMessage.decode bytes).map fun (message, rest) => (.streamCompleteMessage message, rest)
  else if tag = 11 then (SequencedMessage.decode bytes).map fun (message, rest) => (.sequencedMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Data) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Data

/-- Packet -/
structure Packet where
  messageLength : BitVec 16
  data : Data
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUInt 1 (Data.tag message.data)
    ++ (encodeUInt 2 message.messageLength
    ++ (Data.encode message.data))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (messageLength, bytes) ← decodeUInt 2 bytes
  let (data, bytes) ← Data.decode messageType bytes
  pure ({ messageLength, data }, bytes)

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Data.decode_encode, some_bind]
  rfl

end Packet

end Omi.N24x24xequitiesMemoSbeV113
