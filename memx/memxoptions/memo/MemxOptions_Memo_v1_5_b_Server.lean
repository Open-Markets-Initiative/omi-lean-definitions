import Wire

/-!
# The Members Exchange Members Orders v1.5.b

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.MemxMemxoptionsMemoSbeV15BServer

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

/-- Ord Status: one byte code -/
def OrdStatus.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x34, 0x36, 0x38, 0x45, 0x43]

inductive OrdStatus where
  | new -- New
  | partialFilled -- Partial Filled
  | filled -- Filled
  | canceled -- Canceled
  | pendingCancel -- Pending Cancel
  | rejected -- Rejected
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

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x31, 0x32, 0x42]

inductive Side where
  | buy -- Buy
  | sell -- Sell
  | asDefined -- As Defined
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buy => 0x31
  | .sell => 0x32
  | .asDefined => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x31 then .buy
  else if byte = 0x32 then .sell
  else .asDefined

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | asDefined => decide
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
  [0x31, 0x32]

inductive OrdType where
  | market -- Market
  | limit -- Limit
  | unlisted (byte : { byte : UInt8 // byte ∉ OrdType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrdType

def toByte : OrdType → UInt8
  | .market => 0x31
  | .limit => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrdType :=
  if byte = 0x31 then .market
  else .limit

def ofByte (byte : UInt8) : OrdType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrdType) : ofByte value.toByte = value := by
  cases value with
  | market => decide
  | limit => decide
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
  [0x30, 0x33]

inductive TimeInForce where
  | day -- Day
  | immediateOrCancel -- Immediate Or Cancel
  | unlisted (byte : { byte : UInt8 // byte ∉ TimeInForce.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TimeInForce

def toByte : TimeInForce → UInt8
  | .day => 0x30
  | .immediateOrCancel => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TimeInForce :=
  if byte = 0x30 then .day
  else .immediateOrCancel

def ofByte (byte : UInt8) : TimeInForce :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TimeInForce) : ofByte value.toByte = value := by
  cases value with
  | day => decide
  | immediateOrCancel => decide
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

/-- Position Effect Optional: one byte code -/
def PositionEffectOptional.codes : List UInt8 :=
  [0x4F, 0x43]

inductive PositionEffectOptional where
  | open_ -- Open
  | close -- Close
  | unlisted (byte : { byte : UInt8 // byte ∉ PositionEffectOptional.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PositionEffectOptional

def toByte : PositionEffectOptional → UInt8
  | .open_ => 0x4F
  | .close => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PositionEffectOptional :=
  if byte = 0x4F then .open_
  else .close

def ofByte (byte : UInt8) : PositionEffectOptional :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PositionEffectOptional) : ofByte value.toByte = value := by
  cases value with
  | open_ => decide
  | close => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PositionEffectOptional) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PositionEffectOptional × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PositionEffectOptional) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PositionEffectOptional) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PositionEffectOptional

/-- Position Effect: one byte code -/
def PositionEffect.codes : List UInt8 :=
  [0x4F, 0x43]

inductive PositionEffect where
  | open_ -- Open
  | close -- Close
  | unlisted (byte : { byte : UInt8 // byte ∉ PositionEffect.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PositionEffect

def toByte : PositionEffect → UInt8
  | .open_ => 0x4F
  | .close => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PositionEffect :=
  if byte = 0x4F then .open_
  else .close

def ofByte (byte : UInt8) : PositionEffect :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PositionEffect) : ofByte value.toByte = value := by
  cases value with
  | open_ => decide
  | close => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PositionEffect) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PositionEffect × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PositionEffect) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PositionEffect) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PositionEffect

/-- Side Optional: one byte code -/
def SideOptional.codes : List UInt8 :=
  [0x31, 0x32, 0x42]

inductive SideOptional where
  | buy -- Buy
  | sell -- Sell
  | asDefined -- As Defined
  | unlisted (byte : { byte : UInt8 // byte ∉ SideOptional.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SideOptional

def toByte : SideOptional → UInt8
  | .buy => 0x31
  | .sell => 0x32
  | .asDefined => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SideOptional :=
  if byte = 0x31 then .buy
  else if byte = 0x32 then .sell
  else .asDefined

def ofByte (byte : UInt8) : SideOptional :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SideOptional) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | asDefined => decide
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

/-- Alloc Position Effect: one byte code -/
def AllocPositionEffect.codes : List UInt8 :=
  [0x4F, 0x43]

inductive AllocPositionEffect where
  | open_ -- Open
  | close -- Close
  | unlisted (byte : { byte : UInt8 // byte ∉ AllocPositionEffect.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AllocPositionEffect

def toByte : AllocPositionEffect → UInt8
  | .open_ => 0x4F
  | .close => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AllocPositionEffect :=
  if byte = 0x4F then .open_
  else .close

def ofByte (byte : UInt8) : AllocPositionEffect :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AllocPositionEffect) : ofByte value.toByte = value := by
  cases value with
  | open_ => decide
  | close => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AllocPositionEffect) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AllocPositionEffect × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AllocPositionEffect) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AllocPositionEffect) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AllocPositionEffect

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

/-- Parties Group: 18 bytes -/
structure PartiesGroup where
  partyId : Alpha 16
  partyIdSource : Alpha 1
  partyRole : BitVec 8
  deriving DecidableEq, Repr

namespace PartiesGroup

def encode (message : PartiesGroup) : List UInt8 :=
  Alpha.encode message.partyId
    ++ (Alpha.encode message.partyIdSource
    ++ (encodeUInt 1 message.partyRole))

def decode (bytes : List UInt8) : Option (PartiesGroup × List UInt8) := do
  let (partyId, bytes) ← Alpha.decode 16 bytes
  let (partyIdSource, bytes) ← Alpha.decode 1 bytes
  let (partyRole, bytes) ← decodeUInt 1 bytes
  pure ({ partyId, partyIdSource, partyRole }, bytes)

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

/-- Execution Report New Message -/
structure ExecutionReportNewMessage where
  orderId : BitVec 64
  clordid : Alpha 20
  listSeqNo : BitVec 8
  execId : BitVec 64
  ordStatus : OrdStatus
  securityId : Alpha 8
  side : Side
  orderQty : BitVec 32
  ordType : OrdType
  priceOptional : BitVec 64
  timeInForce : TimeInForce
  positionEffectOptional : PositionEffectOptional
  execInst : BitVec 16
  tradingCapacity : BitVec 8
  repriceFrequency : BitVec 8
  repriceBehavior : BitVec 8
  leavesQty : BitVec 32
  cumQty : BitVec 32
  sendingTime : BitVec 64
  transactTime : BitVec 64
  mtpGroupId : BitVec 16
  matchTradePrevention : BitVec 8
  cancelGroupId : BitVec 16
  riskGroupId : BitVec 16
  partiesGroups : PartiesGroups
  deriving DecidableEq, Repr

namespace ExecutionReportNewMessage

def encode (message : ExecutionReportNewMessage) : List UInt8 :=
  encodeUInt 8 message.orderId
    ++ (Alpha.encode message.clordid
    ++ (encodeUInt 1 message.listSeqNo
    ++ (encodeUInt 8 message.execId
    ++ (OrdStatus.encode message.ordStatus
    ++ (Alpha.encode message.securityId
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.orderQty
    ++ (OrdType.encode message.ordType
    ++ (encodeUInt 8 message.priceOptional
    ++ (TimeInForce.encode message.timeInForce
    ++ (PositionEffectOptional.encode message.positionEffectOptional
    ++ (encodeUInt 2 message.execInst
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.repriceFrequency
    ++ (encodeUInt 1 message.repriceBehavior
    ++ (encodeUInt 4 message.leavesQty
    ++ (encodeUInt 4 message.cumQty
    ++ (encodeUInt 8 message.sendingTime
    ++ (encodeUInt 8 message.transactTime
    ++ (encodeUInt 2 message.mtpGroupId
    ++ (encodeUInt 1 message.matchTradePrevention
    ++ (encodeUInt 2 message.cancelGroupId
    ++ (encodeUInt 2 message.riskGroupId
    ++ (PartiesGroups.encode message.partiesGroups))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ExecutionReportNewMessage × List UInt8) := do
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (listSeqNo, bytes) ← decodeUInt 1 bytes
  let (execId, bytes) ← decodeUInt 8 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderQty, bytes) ← decodeUInt 4 bytes
  let (ordType, bytes) ← OrdType.decode bytes
  let (priceOptional, bytes) ← decodeUInt 8 bytes
  let (timeInForce, bytes) ← TimeInForce.decode bytes
  let (positionEffectOptional, bytes) ← PositionEffectOptional.decode bytes
  let (execInst, bytes) ← decodeUInt 2 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (repriceFrequency, bytes) ← decodeUInt 1 bytes
  let (repriceBehavior, bytes) ← decodeUInt 1 bytes
  let (leavesQty, bytes) ← decodeUInt 4 bytes
  let (cumQty, bytes) ← decodeUInt 4 bytes
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (mtpGroupId, bytes) ← decodeUInt 2 bytes
  let (matchTradePrevention, bytes) ← decodeUInt 1 bytes
  let (cancelGroupId, bytes) ← decodeUInt 2 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (partiesGroups, bytes) ← PartiesGroups.decode bytes
  pure ({ orderId, clordid, listSeqNo, execId, ordStatus, securityId, side, orderQty, ordType, priceOptional, timeInForce, positionEffectOptional, execInst, tradingCapacity, repriceFrequency, repriceBehavior, leavesQty, cumQty, sendingTime, transactTime, mtpGroupId, matchTradePrevention, cancelGroupId, riskGroupId, partiesGroups }, bytes)

theorem encode_length_pos (message : ExecutionReportNewMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ExecutionReportNewMessage) : (encode message).length ≤ 4690 := by
  have bound_partiesGroups := PartiesGroups.encode_length_le message.partiesGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OrdStatus.encode_length, Side.encode_length, OrdType.encode_length, TimeInForce.encode_length, PositionEffectOptional.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ExecutionReportNewMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
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
  rw [List.append_assoc, PositionEffectOptional.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [PartiesGroups.decode_encode, some_bind]
  rfl

end ExecutionReportNewMessage

/-- Execution Report Bulk Quote Pending New Message -/
structure ExecutionReportBulkQuotePendingNewMessage where
  clordid : Alpha 20
  symbol : Alpha 6
  timeInForce : TimeInForce
  execInst : BitVec 16
  tradingCapacity : BitVec 8
  sendingTime : BitVec 64
  transactTime : BitVec 64
  mtpGroupId : BitVec 16
  matchTradePrevention : BitVec 8
  cancelGroupId : BitVec 16
  riskGroupId : BitVec 16
  numberOfOrders : BitVec 8
  partiesGroups : PartiesGroups
  deriving DecidableEq, Repr

namespace ExecutionReportBulkQuotePendingNewMessage

def encode (message : ExecutionReportBulkQuotePendingNewMessage) : List UInt8 :=
  Alpha.encode message.clordid
    ++ (Alpha.encode message.symbol
    ++ (TimeInForce.encode message.timeInForce
    ++ (encodeUInt 2 message.execInst
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 8 message.sendingTime
    ++ (encodeUInt 8 message.transactTime
    ++ (encodeUInt 2 message.mtpGroupId
    ++ (encodeUInt 1 message.matchTradePrevention
    ++ (encodeUInt 2 message.cancelGroupId
    ++ (encodeUInt 2 message.riskGroupId
    ++ (encodeUInt 1 message.numberOfOrders
    ++ (PartiesGroups.encode message.partiesGroups))))))))))))

def decode (bytes : List UInt8) : Option (ExecutionReportBulkQuotePendingNewMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (symbol, bytes) ← Alpha.decode 6 bytes
  let (timeInForce, bytes) ← TimeInForce.decode bytes
  let (execInst, bytes) ← decodeUInt 2 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (mtpGroupId, bytes) ← decodeUInt 2 bytes
  let (matchTradePrevention, bytes) ← decodeUInt 1 bytes
  let (cancelGroupId, bytes) ← decodeUInt 2 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (numberOfOrders, bytes) ← decodeUInt 1 bytes
  let (partiesGroups, bytes) ← PartiesGroups.decode bytes
  pure ({ clordid, symbol, timeInForce, execInst, tradingCapacity, sendingTime, transactTime, mtpGroupId, matchTradePrevention, cancelGroupId, riskGroupId, numberOfOrders, partiesGroups }, bytes)

theorem encode_length_pos (message : ExecutionReportBulkQuotePendingNewMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ExecutionReportBulkQuotePendingNewMessage) : (encode message).length ≤ 4646 := by
  have bound_partiesGroups := PartiesGroups.encode_length_le message.partiesGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, TimeInForce.encode_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : ExecutionReportBulkQuotePendingNewMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TimeInForce.decode_encode, some_bind]
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
  rw [PartiesGroups.decode_encode, some_bind]
  rfl

end ExecutionReportBulkQuotePendingNewMessage

/-- Execution Report Bulk Quote Component New Message: 83 bytes -/
structure ExecutionReportBulkQuoteComponentNewMessage where
  orderId : BitVec 64
  clordid : Alpha 20
  listSeqNo : BitVec 8
  execId : BitVec 64
  ordStatus : OrdStatus
  securityId : Alpha 8
  side : Side
  orderQty : BitVec 32
  priceOptional : BitVec 64
  leavesQty : BitVec 32
  cumQty : BitVec 32
  sendingTime : BitVec 64
  transactTime : BitVec 64
  deriving DecidableEq, Repr

namespace ExecutionReportBulkQuoteComponentNewMessage

def encode (message : ExecutionReportBulkQuoteComponentNewMessage) : List UInt8 :=
  encodeUInt 8 message.orderId
    ++ (Alpha.encode message.clordid
    ++ (encodeUInt 1 message.listSeqNo
    ++ (encodeUInt 8 message.execId
    ++ (OrdStatus.encode message.ordStatus
    ++ (Alpha.encode message.securityId
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.orderQty
    ++ (encodeUInt 8 message.priceOptional
    ++ (encodeUInt 4 message.leavesQty
    ++ (encodeUInt 4 message.cumQty
    ++ (encodeUInt 8 message.sendingTime
    ++ (encodeUInt 8 message.transactTime))))))))))))

def decode (bytes : List UInt8) : Option (ExecutionReportBulkQuoteComponentNewMessage × List UInt8) := do
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (listSeqNo, bytes) ← decodeUInt 1 bytes
  let (execId, bytes) ← decodeUInt 8 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderQty, bytes) ← decodeUInt 4 bytes
  let (priceOptional, bytes) ← decodeUInt 8 bytes
  let (leavesQty, bytes) ← decodeUInt 4 bytes
  let (cumQty, bytes) ← decodeUInt 4 bytes
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  pure ({ orderId, clordid, listSeqNo, execId, ordStatus, securityId, side, orderQty, priceOptional, leavesQty, cumQty, sendingTime, transactTime }, bytes)

@[simp] theorem encode_length (message : ExecutionReportBulkQuoteComponentNewMessage) : (encode message).length = 83 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, OrdStatus.encode_length, Side.encode_length]

theorem encode_length_pos (message : ExecutionReportBulkQuoteComponentNewMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutionReportBulkQuoteComponentNewMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ExecutionReportBulkQuoteComponentNewMessage

/-- Execution Report Rejected Message: 57 bytes -/
structure ExecutionReportRejectedMessage where
  clordid : Alpha 20
  listSeqNo : BitVec 8
  execId : BitVec 64
  ordStatus : OrdStatus
  orderRejectReason : BitVec 16
  securityId : Alpha 8
  side : Side
  leavesQty : BitVec 32
  cumQty : BitVec 32
  sendingTime : BitVec 64
  deriving DecidableEq, Repr

namespace ExecutionReportRejectedMessage

def encode (message : ExecutionReportRejectedMessage) : List UInt8 :=
  Alpha.encode message.clordid
    ++ (encodeUInt 1 message.listSeqNo
    ++ (encodeUInt 8 message.execId
    ++ (OrdStatus.encode message.ordStatus
    ++ (encodeUInt 2 message.orderRejectReason
    ++ (Alpha.encode message.securityId
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.leavesQty
    ++ (encodeUInt 4 message.cumQty
    ++ (encodeUInt 8 message.sendingTime)))))))))

def decode (bytes : List UInt8) : Option (ExecutionReportRejectedMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (listSeqNo, bytes) ← decodeUInt 1 bytes
  let (execId, bytes) ← decodeUInt 8 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (orderRejectReason, bytes) ← decodeUInt 2 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (leavesQty, bytes) ← decodeUInt 4 bytes
  let (cumQty, bytes) ← decodeUInt 4 bytes
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  pure ({ clordid, listSeqNo, execId, ordStatus, orderRejectReason, securityId, side, leavesQty, cumQty, sendingTime }, bytes)

@[simp] theorem encode_length (message : ExecutionReportRejectedMessage) : (encode message).length = 57 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, OrdStatus.encode_length, Side.encode_length]

theorem encode_length_pos (message : ExecutionReportRejectedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutionReportRejectedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ExecutionReportRejectedMessage

/-- Execution Report Trade Message -/
structure ExecutionReportTradeMessage where
  orderId : BitVec 64
  clordid : Alpha 20
  listSeqNo : BitVec 8
  trdMatchId : BitVec 64
  execId : BitVec 64
  ordStatus : OrdStatus
  securityId : Alpha 8
  side : Side
  lastQty : BitVec 32
  lastPx : BitVec 64
  leavesQty : BitVec 32
  cumQty : BitVec 32
  sendingTime : BitVec 64
  transactTime : BitVec 64
  lastLiquidityInd : BitVec 8
  lastMkt : Alpha 4
  positionEffect : PositionEffect
  tradingCapacity : BitVec 8
  contraTradingCapacity : BitVec 8
  partiesGroups : PartiesGroups
  deriving DecidableEq, Repr

namespace ExecutionReportTradeMessage

def encode (message : ExecutionReportTradeMessage) : List UInt8 :=
  encodeUInt 8 message.orderId
    ++ (Alpha.encode message.clordid
    ++ (encodeUInt 1 message.listSeqNo
    ++ (encodeUInt 8 message.trdMatchId
    ++ (encodeUInt 8 message.execId
    ++ (OrdStatus.encode message.ordStatus
    ++ (Alpha.encode message.securityId
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.lastQty
    ++ (encodeUInt 8 message.lastPx
    ++ (encodeUInt 4 message.leavesQty
    ++ (encodeUInt 4 message.cumQty
    ++ (encodeUInt 8 message.sendingTime
    ++ (encodeUInt 8 message.transactTime
    ++ (encodeUInt 1 message.lastLiquidityInd
    ++ (Alpha.encode message.lastMkt
    ++ (PositionEffect.encode message.positionEffect
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.contraTradingCapacity
    ++ (PartiesGroups.encode message.partiesGroups)))))))))))))))))))

def decode (bytes : List UInt8) : Option (ExecutionReportTradeMessage × List UInt8) := do
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (listSeqNo, bytes) ← decodeUInt 1 bytes
  let (trdMatchId, bytes) ← decodeUInt 8 bytes
  let (execId, bytes) ← decodeUInt 8 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (lastQty, bytes) ← decodeUInt 4 bytes
  let (lastPx, bytes) ← decodeUInt 8 bytes
  let (leavesQty, bytes) ← decodeUInt 4 bytes
  let (cumQty, bytes) ← decodeUInt 4 bytes
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  let (lastLiquidityInd, bytes) ← decodeUInt 1 bytes
  let (lastMkt, bytes) ← Alpha.decode 4 bytes
  let (positionEffect, bytes) ← PositionEffect.decode bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (contraTradingCapacity, bytes) ← decodeUInt 1 bytes
  let (partiesGroups, bytes) ← PartiesGroups.decode bytes
  pure ({ orderId, clordid, listSeqNo, trdMatchId, execId, ordStatus, securityId, side, lastQty, lastPx, leavesQty, cumQty, sendingTime, transactTime, lastLiquidityInd, lastMkt, positionEffect, tradingCapacity, contraTradingCapacity, partiesGroups }, bytes)

theorem encode_length_pos (message : ExecutionReportTradeMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ExecutionReportTradeMessage) : (encode message).length ≤ 4691 := by
  have bound_partiesGroups := PartiesGroups.encode_length_le message.partiesGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, OrdStatus.encode_length, Side.encode_length, PositionEffect.encode_length]
  omega

@[simp] theorem decode_encode (message : ExecutionReportTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
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
  rw [List.append_assoc, PositionEffect.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [PartiesGroups.decode_encode, some_bind]
  rfl

end ExecutionReportTradeMessage

/-- Execution Report Pending Cancel Message: 75 bytes -/
structure ExecutionReportPendingCancelMessage where
  orderId : BitVec 64
  clordid : Alpha 20
  listSeqNo : BitVec 8
  origclordid : Alpha 20
  ordStatus : OrdStatus
  securityId : Alpha 8
  sideOptional : SideOptional
  leavesQty : BitVec 32
  cumQty : BitVec 32
  sendingTime : BitVec 64
  deriving DecidableEq, Repr

namespace ExecutionReportPendingCancelMessage

def encode (message : ExecutionReportPendingCancelMessage) : List UInt8 :=
  encodeUInt 8 message.orderId
    ++ (Alpha.encode message.clordid
    ++ (encodeUInt 1 message.listSeqNo
    ++ (Alpha.encode message.origclordid
    ++ (OrdStatus.encode message.ordStatus
    ++ (Alpha.encode message.securityId
    ++ (SideOptional.encode message.sideOptional
    ++ (encodeUInt 4 message.leavesQty
    ++ (encodeUInt 4 message.cumQty
    ++ (encodeUInt 8 message.sendingTime)))))))))

def decode (bytes : List UInt8) : Option (ExecutionReportPendingCancelMessage × List UInt8) := do
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (listSeqNo, bytes) ← decodeUInt 1 bytes
  let (origclordid, bytes) ← Alpha.decode 20 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (sideOptional, bytes) ← SideOptional.decode bytes
  let (leavesQty, bytes) ← decodeUInt 4 bytes
  let (cumQty, bytes) ← decodeUInt 4 bytes
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  pure ({ orderId, clordid, listSeqNo, origclordid, ordStatus, securityId, sideOptional, leavesQty, cumQty, sendingTime }, bytes)

@[simp] theorem encode_length (message : ExecutionReportPendingCancelMessage) : (encode message).length = 75 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, OrdStatus.encode_length, SideOptional.encode_length]

theorem encode_length_pos (message : ExecutionReportPendingCancelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutionReportPendingCancelMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
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

end ExecutionReportPendingCancelMessage

/-- Execution Report Canceled Message: 92 bytes -/
structure ExecutionReportCanceledMessage where
  orderId : BitVec 64
  clordid : Alpha 20
  listSeqNo : BitVec 8
  origclordidOptional : Alpha 20
  execId : BitVec 64
  ordStatus : OrdStatus
  cancelReason : BitVec 8
  securityId : Alpha 8
  sideOptional : SideOptional
  leavesQty : BitVec 32
  cumQty : BitVec 32
  sendingTime : BitVec 64
  transactTime : BitVec 64
  deriving DecidableEq, Repr

namespace ExecutionReportCanceledMessage

def encode (message : ExecutionReportCanceledMessage) : List UInt8 :=
  encodeUInt 8 message.orderId
    ++ (Alpha.encode message.clordid
    ++ (encodeUInt 1 message.listSeqNo
    ++ (Alpha.encode message.origclordidOptional
    ++ (encodeUInt 8 message.execId
    ++ (OrdStatus.encode message.ordStatus
    ++ (encodeUInt 1 message.cancelReason
    ++ (Alpha.encode message.securityId
    ++ (SideOptional.encode message.sideOptional
    ++ (encodeUInt 4 message.leavesQty
    ++ (encodeUInt 4 message.cumQty
    ++ (encodeUInt 8 message.sendingTime
    ++ (encodeUInt 8 message.transactTime))))))))))))

def decode (bytes : List UInt8) : Option (ExecutionReportCanceledMessage × List UInt8) := do
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (listSeqNo, bytes) ← decodeUInt 1 bytes
  let (origclordidOptional, bytes) ← Alpha.decode 20 bytes
  let (execId, bytes) ← decodeUInt 8 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (cancelReason, bytes) ← decodeUInt 1 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (sideOptional, bytes) ← SideOptional.decode bytes
  let (leavesQty, bytes) ← decodeUInt 4 bytes
  let (cumQty, bytes) ← decodeUInt 4 bytes
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  pure ({ orderId, clordid, listSeqNo, origclordidOptional, execId, ordStatus, cancelReason, securityId, sideOptional, leavesQty, cumQty, sendingTime, transactTime }, bytes)

@[simp] theorem encode_length (message : ExecutionReportCanceledMessage) : (encode message).length = 92 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, OrdStatus.encode_length, SideOptional.encode_length]

theorem encode_length_pos (message : ExecutionReportCanceledMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutionReportCanceledMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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

end ExecutionReportCanceledMessage

/-- Execution Report Pending Replace Message: 96 bytes -/
structure ExecutionReportPendingReplaceMessage where
  orderId : BitVec 64
  clordid : Alpha 20
  listSeqNo : BitVec 8
  origclordid : Alpha 20
  execId : BitVec 64
  ordStatus : OrdStatus
  securityId : Alpha 8
  side : Side
  orderQty : BitVec 32
  ordType : OrdType
  priceOptional : BitVec 64
  leavesQty : BitVec 32
  cumQty : BitVec 32
  sendingTime : BitVec 64
  deriving DecidableEq, Repr

namespace ExecutionReportPendingReplaceMessage

def encode (message : ExecutionReportPendingReplaceMessage) : List UInt8 :=
  encodeUInt 8 message.orderId
    ++ (Alpha.encode message.clordid
    ++ (encodeUInt 1 message.listSeqNo
    ++ (Alpha.encode message.origclordid
    ++ (encodeUInt 8 message.execId
    ++ (OrdStatus.encode message.ordStatus
    ++ (Alpha.encode message.securityId
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.orderQty
    ++ (OrdType.encode message.ordType
    ++ (encodeUInt 8 message.priceOptional
    ++ (encodeUInt 4 message.leavesQty
    ++ (encodeUInt 4 message.cumQty
    ++ (encodeUInt 8 message.sendingTime)))))))))))))

def decode (bytes : List UInt8) : Option (ExecutionReportPendingReplaceMessage × List UInt8) := do
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (listSeqNo, bytes) ← decodeUInt 1 bytes
  let (origclordid, bytes) ← Alpha.decode 20 bytes
  let (execId, bytes) ← decodeUInt 8 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderQty, bytes) ← decodeUInt 4 bytes
  let (ordType, bytes) ← OrdType.decode bytes
  let (priceOptional, bytes) ← decodeUInt 8 bytes
  let (leavesQty, bytes) ← decodeUInt 4 bytes
  let (cumQty, bytes) ← decodeUInt 4 bytes
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  pure ({ orderId, clordid, listSeqNo, origclordid, execId, ordStatus, securityId, side, orderQty, ordType, priceOptional, leavesQty, cumQty, sendingTime }, bytes)

@[simp] theorem encode_length (message : ExecutionReportPendingReplaceMessage) : (encode message).length = 96 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, OrdStatus.encode_length, Side.encode_length, OrdType.encode_length]

theorem encode_length_pos (message : ExecutionReportPendingReplaceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutionReportPendingReplaceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ExecutionReportPendingReplaceMessage

/-- Execution Report Replaced Message: 104 bytes -/
structure ExecutionReportReplacedMessage where
  orderId : BitVec 64
  clordid : Alpha 20
  listSeqNo : BitVec 8
  origclordid : Alpha 20
  execId : BitVec 64
  ordStatus : OrdStatus
  securityId : Alpha 8
  side : Side
  orderQty : BitVec 32
  ordType : OrdType
  priceOptional : BitVec 64
  leavesQty : BitVec 32
  cumQty : BitVec 32
  sendingTime : BitVec 64
  transactTime : BitVec 64
  deriving DecidableEq, Repr

namespace ExecutionReportReplacedMessage

def encode (message : ExecutionReportReplacedMessage) : List UInt8 :=
  encodeUInt 8 message.orderId
    ++ (Alpha.encode message.clordid
    ++ (encodeUInt 1 message.listSeqNo
    ++ (Alpha.encode message.origclordid
    ++ (encodeUInt 8 message.execId
    ++ (OrdStatus.encode message.ordStatus
    ++ (Alpha.encode message.securityId
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.orderQty
    ++ (OrdType.encode message.ordType
    ++ (encodeUInt 8 message.priceOptional
    ++ (encodeUInt 4 message.leavesQty
    ++ (encodeUInt 4 message.cumQty
    ++ (encodeUInt 8 message.sendingTime
    ++ (encodeUInt 8 message.transactTime))))))))))))))

def decode (bytes : List UInt8) : Option (ExecutionReportReplacedMessage × List UInt8) := do
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (listSeqNo, bytes) ← decodeUInt 1 bytes
  let (origclordid, bytes) ← Alpha.decode 20 bytes
  let (execId, bytes) ← decodeUInt 8 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderQty, bytes) ← decodeUInt 4 bytes
  let (ordType, bytes) ← OrdType.decode bytes
  let (priceOptional, bytes) ← decodeUInt 8 bytes
  let (leavesQty, bytes) ← decodeUInt 4 bytes
  let (cumQty, bytes) ← decodeUInt 4 bytes
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  pure ({ orderId, clordid, listSeqNo, origclordid, execId, ordStatus, securityId, side, orderQty, ordType, priceOptional, leavesQty, cumQty, sendingTime, transactTime }, bytes)

@[simp] theorem encode_length (message : ExecutionReportReplacedMessage) : (encode message).length = 104 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, OrdStatus.encode_length, Side.encode_length, OrdType.encode_length]

theorem encode_length_pos (message : ExecutionReportReplacedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutionReportReplacedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ExecutionReportReplacedMessage

/-- Execution Report Trade Correction Message: 89 bytes -/
structure ExecutionReportTradeCorrectionMessage where
  orderId : BitVec 64
  clordid : Alpha 20
  trdMatchId : BitVec 64
  execId : BitVec 64
  execRefId : BitVec 64
  ordStatus : OrdStatus
  securityId : Alpha 8
  lastQty : BitVec 32
  lastPx : BitVec 64
  leavesQty : BitVec 32
  cumQty : BitVec 32
  sendingTime : BitVec 64
  deriving DecidableEq, Repr

namespace ExecutionReportTradeCorrectionMessage

def encode (message : ExecutionReportTradeCorrectionMessage) : List UInt8 :=
  encodeUInt 8 message.orderId
    ++ (Alpha.encode message.clordid
    ++ (encodeUInt 8 message.trdMatchId
    ++ (encodeUInt 8 message.execId
    ++ (encodeUInt 8 message.execRefId
    ++ (OrdStatus.encode message.ordStatus
    ++ (Alpha.encode message.securityId
    ++ (encodeUInt 4 message.lastQty
    ++ (encodeUInt 8 message.lastPx
    ++ (encodeUInt 4 message.leavesQty
    ++ (encodeUInt 4 message.cumQty
    ++ (encodeUInt 8 message.sendingTime)))))))))))

def decode (bytes : List UInt8) : Option (ExecutionReportTradeCorrectionMessage × List UInt8) := do
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (trdMatchId, bytes) ← decodeUInt 8 bytes
  let (execId, bytes) ← decodeUInt 8 bytes
  let (execRefId, bytes) ← decodeUInt 8 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (lastQty, bytes) ← decodeUInt 4 bytes
  let (lastPx, bytes) ← decodeUInt 8 bytes
  let (leavesQty, bytes) ← decodeUInt 4 bytes
  let (cumQty, bytes) ← decodeUInt 4 bytes
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  pure ({ orderId, clordid, trdMatchId, execId, execRefId, ordStatus, securityId, lastQty, lastPx, leavesQty, cumQty, sendingTime }, bytes)

@[simp] theorem encode_length (message : ExecutionReportTradeCorrectionMessage) : (encode message).length = 89 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, OrdStatus.encode_length]

theorem encode_length_pos (message : ExecutionReportTradeCorrectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutionReportTradeCorrectionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ExecutionReportTradeCorrectionMessage

/-- Execution Report Trade Break Message: 77 bytes -/
structure ExecutionReportTradeBreakMessage where
  orderId : BitVec 64
  clordid : Alpha 20
  trdMatchId : BitVec 64
  execId : BitVec 64
  execRefId : BitVec 64
  ordStatus : OrdStatus
  securityId : Alpha 8
  leavesQty : BitVec 32
  cumQty : BitVec 32
  sendingTime : BitVec 64
  deriving DecidableEq, Repr

namespace ExecutionReportTradeBreakMessage

def encode (message : ExecutionReportTradeBreakMessage) : List UInt8 :=
  encodeUInt 8 message.orderId
    ++ (Alpha.encode message.clordid
    ++ (encodeUInt 8 message.trdMatchId
    ++ (encodeUInt 8 message.execId
    ++ (encodeUInt 8 message.execRefId
    ++ (OrdStatus.encode message.ordStatus
    ++ (Alpha.encode message.securityId
    ++ (encodeUInt 4 message.leavesQty
    ++ (encodeUInt 4 message.cumQty
    ++ (encodeUInt 8 message.sendingTime)))))))))

def decode (bytes : List UInt8) : Option (ExecutionReportTradeBreakMessage × List UInt8) := do
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (trdMatchId, bytes) ← decodeUInt 8 bytes
  let (execId, bytes) ← decodeUInt 8 bytes
  let (execRefId, bytes) ← decodeUInt 8 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (leavesQty, bytes) ← decodeUInt 4 bytes
  let (cumQty, bytes) ← decodeUInt 4 bytes
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  pure ({ orderId, clordid, trdMatchId, execId, execRefId, ordStatus, securityId, leavesQty, cumQty, sendingTime }, bytes)

@[simp] theorem encode_length (message : ExecutionReportTradeBreakMessage) : (encode message).length = 77 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, OrdStatus.encode_length]

theorem encode_length_pos (message : ExecutionReportTradeBreakMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutionReportTradeBreakMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ExecutionReportTradeBreakMessage

/-- Execution Report Restatement Message: 85 bytes -/
structure ExecutionReportRestatementMessage where
  orderId : BitVec 64
  clordid : Alpha 20
  listSeqNo : BitVec 8
  execId : BitVec 64
  ordStatus : OrdStatus
  securityId : Alpha 8
  execRestatementReason : BitVec 8
  extendedRestatementReason : BitVec 8
  side : Side
  lastPx : BitVec 64
  lastQtyOptional : BitVec 32
  leavesQty : BitVec 32
  cumQty : BitVec 32
  sendingTime : BitVec 64
  transactTime : BitVec 64
  deriving DecidableEq, Repr

namespace ExecutionReportRestatementMessage

def encode (message : ExecutionReportRestatementMessage) : List UInt8 :=
  encodeUInt 8 message.orderId
    ++ (Alpha.encode message.clordid
    ++ (encodeUInt 1 message.listSeqNo
    ++ (encodeUInt 8 message.execId
    ++ (OrdStatus.encode message.ordStatus
    ++ (Alpha.encode message.securityId
    ++ (encodeUInt 1 message.execRestatementReason
    ++ (encodeUInt 1 message.extendedRestatementReason
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.lastPx
    ++ (encodeUInt 4 message.lastQtyOptional
    ++ (encodeUInt 4 message.leavesQty
    ++ (encodeUInt 4 message.cumQty
    ++ (encodeUInt 8 message.sendingTime
    ++ (encodeUInt 8 message.transactTime))))))))))))))

def decode (bytes : List UInt8) : Option (ExecutionReportRestatementMessage × List UInt8) := do
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (listSeqNo, bytes) ← decodeUInt 1 bytes
  let (execId, bytes) ← decodeUInt 8 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (execRestatementReason, bytes) ← decodeUInt 1 bytes
  let (extendedRestatementReason, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← Side.decode bytes
  let (lastPx, bytes) ← decodeUInt 8 bytes
  let (lastQtyOptional, bytes) ← decodeUInt 4 bytes
  let (leavesQty, bytes) ← decodeUInt 4 bytes
  let (cumQty, bytes) ← decodeUInt 4 bytes
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  let (transactTime, bytes) ← decodeUInt 8 bytes
  pure ({ orderId, clordid, listSeqNo, execId, ordStatus, securityId, execRestatementReason, extendedRestatementReason, side, lastPx, lastQtyOptional, leavesQty, cumQty, sendingTime, transactTime }, bytes)

@[simp] theorem encode_length (message : ExecutionReportRestatementMessage) : (encode message).length = 85 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, OrdStatus.encode_length, Side.encode_length]

theorem encode_length_pos (message : ExecutionReportRestatementMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutionReportRestatementMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ExecutionReportRestatementMessage

/-- Pending Mass Cancel Message: 58 bytes -/
structure PendingMassCancelMessage where
  clordid : Alpha 20
  massCancelInst : BitVec 8
  lockoutIdOptional : BitVec 64
  efidOptional : Alpha 4
  underlyingOrSeries : BitVec 8
  underlier : Alpha 6
  optionsSecurityIdOptional : Alpha 8
  cancelGroupId : BitVec 16
  sendingTime : BitVec 64
  deriving DecidableEq, Repr

namespace PendingMassCancelMessage

def encode (message : PendingMassCancelMessage) : List UInt8 :=
  Alpha.encode message.clordid
    ++ (encodeUIntLE 1 message.massCancelInst
    ++ (encodeUInt 8 message.lockoutIdOptional
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 1 message.underlyingOrSeries
    ++ (Alpha.encode message.underlier
    ++ (Alpha.encode message.optionsSecurityIdOptional
    ++ (encodeUInt 2 message.cancelGroupId
    ++ (encodeUInt 8 message.sendingTime))))))))

def decode (bytes : List UInt8) : Option (PendingMassCancelMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (massCancelInst, bytes) ← decodeUIntLE 1 bytes
  let (lockoutIdOptional, bytes) ← decodeUInt 8 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (underlyingOrSeries, bytes) ← decodeUInt 1 bytes
  let (underlier, bytes) ← Alpha.decode 6 bytes
  let (optionsSecurityIdOptional, bytes) ← Alpha.decode 8 bytes
  let (cancelGroupId, bytes) ← decodeUInt 2 bytes
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  pure ({ clordid, massCancelInst, lockoutIdOptional, efidOptional, underlyingOrSeries, underlier, optionsSecurityIdOptional, cancelGroupId, sendingTime }, bytes)

@[simp] theorem encode_length (message : PendingMassCancelMessage) : (encode message).length = 58 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : PendingMassCancelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PendingMassCancelMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end PendingMassCancelMessage

/-- Mass Cancel Reject Message: 52 bytes -/
structure MassCancelRejectMessage where
  clordid : Alpha 20
  massCancelRejectReason : BitVec 16
  efidOptional : Alpha 4
  underlyingOrSeriesOptional : BitVec 8
  underlierOptional : Alpha 6
  optionsSecurityIdOptional : Alpha 8
  cancelGroupId : BitVec 16
  massCancelInst : BitVec 8
  sendingTime : BitVec 64
  deriving DecidableEq, Repr

namespace MassCancelRejectMessage

def encode (message : MassCancelRejectMessage) : List UInt8 :=
  Alpha.encode message.clordid
    ++ (encodeUInt 2 message.massCancelRejectReason
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 1 message.underlyingOrSeriesOptional
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.optionsSecurityIdOptional
    ++ (encodeUInt 2 message.cancelGroupId
    ++ (encodeUIntLE 1 message.massCancelInst
    ++ (encodeUInt 8 message.sendingTime))))))))

def decode (bytes : List UInt8) : Option (MassCancelRejectMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (massCancelRejectReason, bytes) ← decodeUInt 2 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (underlyingOrSeriesOptional, bytes) ← decodeUInt 1 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (optionsSecurityIdOptional, bytes) ← Alpha.decode 8 bytes
  let (cancelGroupId, bytes) ← decodeUInt 2 bytes
  let (massCancelInst, bytes) ← decodeUIntLE 1 bytes
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  pure ({ clordid, massCancelRejectReason, efidOptional, underlyingOrSeriesOptional, underlierOptional, optionsSecurityIdOptional, cancelGroupId, massCancelInst, sendingTime }, bytes)

@[simp] theorem encode_length (message : MassCancelRejectMessage) : (encode message).length = 52 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, encodeUIntLE_length]

theorem encode_length_pos (message : MassCancelRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassCancelRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MassCancelRejectMessage

/-- Mass Cancel Done Message: 32 bytes -/
structure MassCancelDoneMessage where
  clordid : Alpha 20
  totalAffectedOrders : BitVec 32
  sendingTime : BitVec 64
  deriving DecidableEq, Repr

namespace MassCancelDoneMessage

def encode (message : MassCancelDoneMessage) : List UInt8 :=
  Alpha.encode message.clordid
    ++ (encodeUInt 4 message.totalAffectedOrders
    ++ (encodeUInt 8 message.sendingTime))

def decode (bytes : List UInt8) : Option (MassCancelDoneMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (totalAffectedOrders, bytes) ← decodeUInt 4 bytes
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  pure ({ clordid, totalAffectedOrders, sendingTime }, bytes)

@[simp] theorem encode_length (message : MassCancelDoneMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : MassCancelDoneMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassCancelDoneMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MassCancelDoneMessage

/-- Order Cancel Reject Message: 41 bytes -/
structure OrderCancelRejectMessage where
  clordid : Alpha 20
  listSeqNo : BitVec 8
  cxlRejResponseTo : CxlRejResponseTo
  cxlRejReason : BitVec 16
  optionsSecurityIdOptional : Alpha 8
  sideOptional : SideOptional
  sendingTime : BitVec 64
  deriving DecidableEq, Repr

namespace OrderCancelRejectMessage

def encode (message : OrderCancelRejectMessage) : List UInt8 :=
  Alpha.encode message.clordid
    ++ (encodeUInt 1 message.listSeqNo
    ++ (CxlRejResponseTo.encode message.cxlRejResponseTo
    ++ (encodeUInt 2 message.cxlRejReason
    ++ (Alpha.encode message.optionsSecurityIdOptional
    ++ (SideOptional.encode message.sideOptional
    ++ (encodeUInt 8 message.sendingTime))))))

def decode (bytes : List UInt8) : Option (OrderCancelRejectMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (listSeqNo, bytes) ← decodeUInt 1 bytes
  let (cxlRejResponseTo, bytes) ← CxlRejResponseTo.decode bytes
  let (cxlRejReason, bytes) ← decodeUInt 2 bytes
  let (optionsSecurityIdOptional, bytes) ← Alpha.decode 8 bytes
  let (sideOptional, bytes) ← SideOptional.decode bytes
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  pure ({ clordid, listSeqNo, cxlRejResponseTo, cxlRejReason, optionsSecurityIdOptional, sideOptional, sendingTime }, bytes)

@[simp] theorem encode_length (message : OrderCancelRejectMessage) : (encode message).length = 41 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, CxlRejResponseTo.encode_length, SideOptional.encode_length]

theorem encode_length_pos (message : OrderCancelRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancelRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, CxlRejResponseTo.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SideOptional.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderCancelRejectMessage

/-- Nested Parties Group: 18 bytes -/
structure NestedPartiesGroup where
  nestedPartyId : Alpha 16
  nestedPartyIdSource : Alpha 1
  nestedPartyRole : BitVec 8
  deriving DecidableEq, Repr

namespace NestedPartiesGroup

def encode (message : NestedPartiesGroup) : List UInt8 :=
  Alpha.encode message.nestedPartyId
    ++ (Alpha.encode message.nestedPartyIdSource
    ++ (encodeUInt 1 message.nestedPartyRole))

def decode (bytes : List UInt8) : Option (NestedPartiesGroup × List UInt8) := do
  let (nestedPartyId, bytes) ← Alpha.decode 16 bytes
  let (nestedPartyIdSource, bytes) ← Alpha.decode 1 bytes
  let (nestedPartyRole, bytes) ← decodeUInt 1 bytes
  pure ({ nestedPartyId, nestedPartyIdSource, nestedPartyRole }, bytes)

@[simp] theorem encode_length (message : NestedPartiesGroup) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : NestedPartiesGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NestedPartiesGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end NestedPartiesGroup

/-- Nested Parties Groups -/
structure NestedPartiesGroups where
  blockLengthShort : BitVec 8
  nestedPartiesGroup : Bounded 1 NestedPartiesGroup
  deriving DecidableEq, Repr

namespace NestedPartiesGroups

def encode (message : NestedPartiesGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.nestedPartiesGroup.val.length)
    ++ (encodeMany NestedPartiesGroup.encode message.nestedPartiesGroup.val))

def decode (bytes : List UInt8) : Option (NestedPartiesGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (nestedPartiesGroup_, bytes) ← decodeMany NestedPartiesGroup.decode numInGroup.toNat bytes
  if fits_nestedPartiesGroup : nestedPartiesGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, nestedPartiesGroup := ⟨nestedPartiesGroup_, fits_nestedPartiesGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : NestedPartiesGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : NestedPartiesGroups) : (encode message).length ≤ 4592 := by
  have bound_nestedPartiesGroup := message.nestedPartiesGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const NestedPartiesGroup.encode 18 NestedPartiesGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : NestedPartiesGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 NestedPartiesGroup.encode NestedPartiesGroup.decode NestedPartiesGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.nestedPartiesGroup.length_lt]
  rfl

end NestedPartiesGroups

/-- Reported Allocations Group -/
structure ReportedAllocationsGroup where
  allocQty : BitVec 32
  allocPositionEffect : AllocPositionEffect
  allocId : Alpha 20
  nestedPartiesGroups : NestedPartiesGroups
  deriving DecidableEq, Repr

namespace ReportedAllocationsGroup

def encode (message : ReportedAllocationsGroup) : List UInt8 :=
  encodeUInt 4 message.allocQty
    ++ (AllocPositionEffect.encode message.allocPositionEffect
    ++ (Alpha.encode message.allocId
    ++ (NestedPartiesGroups.encode message.nestedPartiesGroups)))

def decode (bytes : List UInt8) : Option (ReportedAllocationsGroup × List UInt8) := do
  let (allocQty, bytes) ← decodeUInt 4 bytes
  let (allocPositionEffect, bytes) ← AllocPositionEffect.decode bytes
  let (allocId, bytes) ← Alpha.decode 20 bytes
  let (nestedPartiesGroups, bytes) ← NestedPartiesGroups.decode bytes
  pure ({ allocQty, allocPositionEffect, allocId, nestedPartiesGroups }, bytes)

theorem encode_length_pos (message : ReportedAllocationsGroup) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ReportedAllocationsGroup) : (encode message).length ≤ 4617 := by
  have bound_nestedPartiesGroups := NestedPartiesGroups.encode_length_le message.nestedPartiesGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, AllocPositionEffect.encode_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : ReportedAllocationsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, AllocPositionEffect.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [NestedPartiesGroups.decode_encode, some_bind]
  rfl

end ReportedAllocationsGroup

/-- Reported Allocations Groups -/
structure ReportedAllocationsGroups where
  blockLengthShort : BitVec 8
  reportedAllocationsGroup : Bounded 1 ReportedAllocationsGroup
  deriving DecidableEq, Repr

namespace ReportedAllocationsGroups

def encode (message : ReportedAllocationsGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.reportedAllocationsGroup.val.length)
    ++ (encodeMany ReportedAllocationsGroup.encode message.reportedAllocationsGroup.val))

def decode (bytes : List UInt8) : Option (ReportedAllocationsGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (reportedAllocationsGroup_, bytes) ← decodeMany ReportedAllocationsGroup.decode numInGroup.toNat bytes
  if fits_reportedAllocationsGroup : reportedAllocationsGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, reportedAllocationsGroup := ⟨reportedAllocationsGroup_, fits_reportedAllocationsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : ReportedAllocationsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ReportedAllocationsGroups) : (encode message).length ≤ 1177337 := by
  have bound_reportedAllocationsGroup := message.reportedAllocationsGroup.length_lt
  have bound_reportedAllocationsGroup_items := encodeMany_length_le ReportedAllocationsGroup.encode 4617 ReportedAllocationsGroup.encode_length_le message.reportedAllocationsGroup.val
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : ReportedAllocationsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 ReportedAllocationsGroup.encode ReportedAllocationsGroup.decode ReportedAllocationsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.reportedAllocationsGroup.length_lt]
  rfl

end ReportedAllocationsGroups

/-- Allocation Instruction Ack Message -/
structure AllocationInstructionAckMessage where
  sendingTime : BitVec 64
  allocId : Alpha 20
  allocType : BitVec 8
  allocTransType : BitVec 8
  secondaryAllocId : Alpha 20
  refAllocIdOptional : Alpha 20
  allocStatus : BitVec 8
  allocRejCode : BitVec 16
  reportedAllocationsGroups : ReportedAllocationsGroups
  deriving DecidableEq, Repr

namespace AllocationInstructionAckMessage

def encode (message : AllocationInstructionAckMessage) : List UInt8 :=
  encodeUInt 8 message.sendingTime
    ++ (Alpha.encode message.allocId
    ++ (encodeUInt 1 message.allocType
    ++ (encodeUInt 1 message.allocTransType
    ++ (Alpha.encode message.secondaryAllocId
    ++ (Alpha.encode message.refAllocIdOptional
    ++ (encodeUInt 1 message.allocStatus
    ++ (encodeUInt 2 message.allocRejCode
    ++ (ReportedAllocationsGroups.encode message.reportedAllocationsGroups))))))))

def decode (bytes : List UInt8) : Option (AllocationInstructionAckMessage × List UInt8) := do
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  let (allocId, bytes) ← Alpha.decode 20 bytes
  let (allocType, bytes) ← decodeUInt 1 bytes
  let (allocTransType, bytes) ← decodeUInt 1 bytes
  let (secondaryAllocId, bytes) ← Alpha.decode 20 bytes
  let (refAllocIdOptional, bytes) ← Alpha.decode 20 bytes
  let (allocStatus, bytes) ← decodeUInt 1 bytes
  let (allocRejCode, bytes) ← decodeUInt 2 bytes
  let (reportedAllocationsGroups, bytes) ← ReportedAllocationsGroups.decode bytes
  pure ({ sendingTime, allocId, allocType, allocTransType, secondaryAllocId, refAllocIdOptional, allocStatus, allocRejCode, reportedAllocationsGroups }, bytes)

theorem encode_length_pos (message : AllocationInstructionAckMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : AllocationInstructionAckMessage) : (encode message).length ≤ 1177410 := by
  have bound_reportedAllocationsGroups := ReportedAllocationsGroups.encode_length_le message.reportedAllocationsGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : AllocationInstructionAckMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ReportedAllocationsGroups.decode_encode, some_bind]
  rfl

end AllocationInstructionAckMessage

/-- Execution Allocations Group: 20 bytes -/
structure ExecutionAllocationsGroup where
  tradeId : BitVec 64
  lastQty : BitVec 32
  lastPx : BitVec 64
  deriving DecidableEq, Repr

namespace ExecutionAllocationsGroup

def encode (message : ExecutionAllocationsGroup) : List UInt8 :=
  encodeUInt 8 message.tradeId
    ++ (encodeUInt 4 message.lastQty
    ++ (encodeUInt 8 message.lastPx))

def decode (bytes : List UInt8) : Option (ExecutionAllocationsGroup × List UInt8) := do
  let (tradeId, bytes) ← decodeUInt 8 bytes
  let (lastQty, bytes) ← decodeUInt 4 bytes
  let (lastPx, bytes) ← decodeUInt 8 bytes
  pure ({ tradeId, lastQty, lastPx }, bytes)

@[simp] theorem encode_length (message : ExecutionAllocationsGroup) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : ExecutionAllocationsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutionAllocationsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ExecutionAllocationsGroup

/-- Execution Allocations Groups -/
structure ExecutionAllocationsGroups where
  blockLengthShort : BitVec 8
  executionAllocationsGroup : Bounded 1 ExecutionAllocationsGroup
  deriving DecidableEq, Repr

namespace ExecutionAllocationsGroups

def encode (message : ExecutionAllocationsGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.executionAllocationsGroup.val.length)
    ++ (encodeMany ExecutionAllocationsGroup.encode message.executionAllocationsGroup.val))

def decode (bytes : List UInt8) : Option (ExecutionAllocationsGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (executionAllocationsGroup_, bytes) ← decodeMany ExecutionAllocationsGroup.decode numInGroup.toNat bytes
  if fits_executionAllocationsGroup : executionAllocationsGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, executionAllocationsGroup := ⟨executionAllocationsGroup_, fits_executionAllocationsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : ExecutionAllocationsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ExecutionAllocationsGroups) : (encode message).length ≤ 5102 := by
  have bound_executionAllocationsGroup := message.executionAllocationsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const ExecutionAllocationsGroup.encode 20 ExecutionAllocationsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : ExecutionAllocationsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 ExecutionAllocationsGroup.encode ExecutionAllocationsGroup.decode ExecutionAllocationsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.executionAllocationsGroup.length_lt]
  rfl

end ExecutionAllocationsGroups

/-- Allocation Instruction Alert Message -/
structure AllocationInstructionAlertMessage where
  sendingTime : BitVec 64
  allocId : Alpha 20
  allocType : BitVec 8
  allocTransType : BitVec 8
  refAllocIdOptional : Alpha 20
  allocCancReplaceReason : BitVec 16
  side : Side
  securityId : Alpha 8
  tradeDate : Alpha 8
  executionAllocationsGroups : ExecutionAllocationsGroups
  reportedAllocationsGroups : ReportedAllocationsGroups
  deriving DecidableEq, Repr

namespace AllocationInstructionAlertMessage

def encode (message : AllocationInstructionAlertMessage) : List UInt8 :=
  encodeUInt 8 message.sendingTime
    ++ (Alpha.encode message.allocId
    ++ (encodeUInt 1 message.allocType
    ++ (encodeUInt 1 message.allocTransType
    ++ (Alpha.encode message.refAllocIdOptional
    ++ (encodeUInt 2 message.allocCancReplaceReason
    ++ (Side.encode message.side
    ++ (Alpha.encode message.securityId
    ++ (Alpha.encode message.tradeDate
    ++ (ExecutionAllocationsGroups.encode message.executionAllocationsGroups
    ++ (ReportedAllocationsGroups.encode message.reportedAllocationsGroups))))))))))

def decode (bytes : List UInt8) : Option (AllocationInstructionAlertMessage × List UInt8) := do
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  let (allocId, bytes) ← Alpha.decode 20 bytes
  let (allocType, bytes) ← decodeUInt 1 bytes
  let (allocTransType, bytes) ← decodeUInt 1 bytes
  let (refAllocIdOptional, bytes) ← Alpha.decode 20 bytes
  let (allocCancReplaceReason, bytes) ← decodeUInt 2 bytes
  let (side, bytes) ← Side.decode bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (tradeDate, bytes) ← Alpha.decode 8 bytes
  let (executionAllocationsGroups, bytes) ← ExecutionAllocationsGroups.decode bytes
  let (reportedAllocationsGroups, bytes) ← ReportedAllocationsGroups.decode bytes
  pure ({ sendingTime, allocId, allocType, allocTransType, refAllocIdOptional, allocCancReplaceReason, side, securityId, tradeDate, executionAllocationsGroups, reportedAllocationsGroups }, bytes)

theorem encode_length_pos (message : AllocationInstructionAlertMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : AllocationInstructionAlertMessage) : (encode message).length ≤ 1182508 := by
  have bound_executionAllocationsGroups := ExecutionAllocationsGroups.encode_length_le message.executionAllocationsGroups
  have bound_reportedAllocationsGroups := ReportedAllocationsGroups.encode_length_le message.reportedAllocationsGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, Side.encode_length]
  omega

@[simp] theorem decode_encode (message : AllocationInstructionAlertMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecutionAllocationsGroups.decode_encode, some_bind]
  dsimp only
  rw [ReportedAllocationsGroups.decode_encode, some_bind]
  rfl

end AllocationInstructionAlertMessage

/-- User Notification Message: 9 bytes -/
structure UserNotificationMessage where
  sendingTime : BitVec 64
  userStatus : BitVec 8
  deriving DecidableEq, Repr

namespace UserNotificationMessage

def encode (message : UserNotificationMessage) : List UInt8 :=
  encodeUInt 8 message.sendingTime
    ++ (encodeUInt 1 message.userStatus)

def decode (bytes : List UInt8) : Option (UserNotificationMessage × List UInt8) := do
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  let (userStatus, bytes) ← decodeUInt 1 bytes
  pure ({ sendingTime, userStatus }, bytes)

@[simp] theorem encode_length (message : UserNotificationMessage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : UserNotificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserNotificationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end UserNotificationMessage

/-- Mass Cancel Clear Lockout Reject Message: 38 bytes -/
structure MassCancelClearLockoutRejectMessage where
  clordid : Alpha 20
  lockoutId : BitVec 64
  rejReason : BitVec 16
  sendingTime : BitVec 64
  deriving DecidableEq, Repr

namespace MassCancelClearLockoutRejectMessage

def encode (message : MassCancelClearLockoutRejectMessage) : List UInt8 :=
  Alpha.encode message.clordid
    ++ (encodeUInt 8 message.lockoutId
    ++ (encodeUInt 2 message.rejReason
    ++ (encodeUInt 8 message.sendingTime)))

def decode (bytes : List UInt8) : Option (MassCancelClearLockoutRejectMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (lockoutId, bytes) ← decodeUInt 8 bytes
  let (rejReason, bytes) ← decodeUInt 2 bytes
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  pure ({ clordid, lockoutId, rejReason, sendingTime }, bytes)

@[simp] theorem encode_length (message : MassCancelClearLockoutRejectMessage) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : MassCancelClearLockoutRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassCancelClearLockoutRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MassCancelClearLockoutRejectMessage

/-- Mass Cancel Clear Lockout Done Message: 36 bytes -/
structure MassCancelClearLockoutDoneMessage where
  clordid : Alpha 20
  lockoutId : BitVec 64
  sendingTime : BitVec 64
  deriving DecidableEq, Repr

namespace MassCancelClearLockoutDoneMessage

def encode (message : MassCancelClearLockoutDoneMessage) : List UInt8 :=
  Alpha.encode message.clordid
    ++ (encodeUInt 8 message.lockoutId
    ++ (encodeUInt 8 message.sendingTime))

def decode (bytes : List UInt8) : Option (MassCancelClearLockoutDoneMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (lockoutId, bytes) ← decodeUInt 8 bytes
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  pure ({ clordid, lockoutId, sendingTime }, bytes)

@[simp] theorem encode_length (message : MassCancelClearLockoutDoneMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : MassCancelClearLockoutDoneMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassCancelClearLockoutDoneMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MassCancelClearLockoutDoneMessage

/-- Any Server Payload, selected by Template Id -/
inductive ServerPayload where
  | executionReportNewMessage (message : ExecutionReportNewMessage) -- 11
  | executionReportBulkQuotePendingNewMessage (message : ExecutionReportBulkQuotePendingNewMessage) -- 12
  | executionReportBulkQuoteComponentNewMessage (message : ExecutionReportBulkQuoteComponentNewMessage) -- 13
  | executionReportRejectedMessage (message : ExecutionReportRejectedMessage) -- 14
  | executionReportTradeMessage (message : ExecutionReportTradeMessage) -- 15
  | executionReportPendingCancelMessage (message : ExecutionReportPendingCancelMessage) -- 16
  | executionReportCanceledMessage (message : ExecutionReportCanceledMessage) -- 17
  | executionReportPendingReplaceMessage (message : ExecutionReportPendingReplaceMessage) -- 18
  | executionReportReplacedMessage (message : ExecutionReportReplacedMessage) -- 19
  | executionReportTradeCorrectionMessage (message : ExecutionReportTradeCorrectionMessage) -- 20
  | executionReportTradeBreakMessage (message : ExecutionReportTradeBreakMessage) -- 21
  | executionReportRestatementMessage (message : ExecutionReportRestatementMessage) -- 22
  | pendingMassCancelMessage (message : PendingMassCancelMessage) -- 23
  | massCancelRejectMessage (message : MassCancelRejectMessage) -- 24
  | massCancelDoneMessage (message : MassCancelDoneMessage) -- 25
  | orderCancelRejectMessage (message : OrderCancelRejectMessage) -- 26
  | allocationInstructionAckMessage (message : AllocationInstructionAckMessage) -- 27
  | allocationInstructionAlertMessage (message : AllocationInstructionAlertMessage) -- 28
  | userNotificationMessage (message : UserNotificationMessage) -- 29
  | massCancelClearLockoutRejectMessage (message : MassCancelClearLockoutRejectMessage) -- 30
  | massCancelClearLockoutDoneMessage (message : MassCancelClearLockoutDoneMessage) -- 31
  deriving DecidableEq, Repr

namespace ServerPayload

/-- The Template Id each message is sent under -/
def tag : ServerPayload → BitVec 8
  | .executionReportNewMessage _ => 11
  | .executionReportBulkQuotePendingNewMessage _ => 12
  | .executionReportBulkQuoteComponentNewMessage _ => 13
  | .executionReportRejectedMessage _ => 14
  | .executionReportTradeMessage _ => 15
  | .executionReportPendingCancelMessage _ => 16
  | .executionReportCanceledMessage _ => 17
  | .executionReportPendingReplaceMessage _ => 18
  | .executionReportReplacedMessage _ => 19
  | .executionReportTradeCorrectionMessage _ => 20
  | .executionReportTradeBreakMessage _ => 21
  | .executionReportRestatementMessage _ => 22
  | .pendingMassCancelMessage _ => 23
  | .massCancelRejectMessage _ => 24
  | .massCancelDoneMessage _ => 25
  | .orderCancelRejectMessage _ => 26
  | .allocationInstructionAckMessage _ => 27
  | .allocationInstructionAlertMessage _ => 28
  | .userNotificationMessage _ => 29
  | .massCancelClearLockoutRejectMessage _ => 30
  | .massCancelClearLockoutDoneMessage _ => 31

def encode : ServerPayload → List UInt8
  | .executionReportNewMessage message => ExecutionReportNewMessage.encode message
  | .executionReportBulkQuotePendingNewMessage message => ExecutionReportBulkQuotePendingNewMessage.encode message
  | .executionReportBulkQuoteComponentNewMessage message => ExecutionReportBulkQuoteComponentNewMessage.encode message
  | .executionReportRejectedMessage message => ExecutionReportRejectedMessage.encode message
  | .executionReportTradeMessage message => ExecutionReportTradeMessage.encode message
  | .executionReportPendingCancelMessage message => ExecutionReportPendingCancelMessage.encode message
  | .executionReportCanceledMessage message => ExecutionReportCanceledMessage.encode message
  | .executionReportPendingReplaceMessage message => ExecutionReportPendingReplaceMessage.encode message
  | .executionReportReplacedMessage message => ExecutionReportReplacedMessage.encode message
  | .executionReportTradeCorrectionMessage message => ExecutionReportTradeCorrectionMessage.encode message
  | .executionReportTradeBreakMessage message => ExecutionReportTradeBreakMessage.encode message
  | .executionReportRestatementMessage message => ExecutionReportRestatementMessage.encode message
  | .pendingMassCancelMessage message => PendingMassCancelMessage.encode message
  | .massCancelRejectMessage message => MassCancelRejectMessage.encode message
  | .massCancelDoneMessage message => MassCancelDoneMessage.encode message
  | .orderCancelRejectMessage message => OrderCancelRejectMessage.encode message
  | .allocationInstructionAckMessage message => AllocationInstructionAckMessage.encode message
  | .allocationInstructionAlertMessage message => AllocationInstructionAlertMessage.encode message
  | .userNotificationMessage message => UserNotificationMessage.encode message
  | .massCancelClearLockoutRejectMessage message => MassCancelClearLockoutRejectMessage.encode message
  | .massCancelClearLockoutDoneMessage message => MassCancelClearLockoutDoneMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ServerPayload) : (encode message).length ≤ 1182508 := by
  cases message with
  | executionReportNewMessage inner =>
    have bound_inner := ExecutionReportNewMessage.encode_length_le inner
    simp only [encode]
    omega
  | executionReportBulkQuotePendingNewMessage inner =>
    have bound_inner := ExecutionReportBulkQuotePendingNewMessage.encode_length_le inner
    simp only [encode]
    omega
  | executionReportBulkQuoteComponentNewMessage inner =>
    simp only [encode, ExecutionReportBulkQuoteComponentNewMessage.encode_length]
    omega
  | executionReportRejectedMessage inner =>
    simp only [encode, ExecutionReportRejectedMessage.encode_length]
    omega
  | executionReportTradeMessage inner =>
    have bound_inner := ExecutionReportTradeMessage.encode_length_le inner
    simp only [encode]
    omega
  | executionReportPendingCancelMessage inner =>
    simp only [encode, ExecutionReportPendingCancelMessage.encode_length]
    omega
  | executionReportCanceledMessage inner =>
    simp only [encode, ExecutionReportCanceledMessage.encode_length]
    omega
  | executionReportPendingReplaceMessage inner =>
    simp only [encode, ExecutionReportPendingReplaceMessage.encode_length]
    omega
  | executionReportReplacedMessage inner =>
    simp only [encode, ExecutionReportReplacedMessage.encode_length]
    omega
  | executionReportTradeCorrectionMessage inner =>
    simp only [encode, ExecutionReportTradeCorrectionMessage.encode_length]
    omega
  | executionReportTradeBreakMessage inner =>
    simp only [encode, ExecutionReportTradeBreakMessage.encode_length]
    omega
  | executionReportRestatementMessage inner =>
    simp only [encode, ExecutionReportRestatementMessage.encode_length]
    omega
  | pendingMassCancelMessage inner =>
    simp only [encode, PendingMassCancelMessage.encode_length]
    omega
  | massCancelRejectMessage inner =>
    simp only [encode, MassCancelRejectMessage.encode_length]
    omega
  | massCancelDoneMessage inner =>
    simp only [encode, MassCancelDoneMessage.encode_length]
    omega
  | orderCancelRejectMessage inner =>
    simp only [encode, OrderCancelRejectMessage.encode_length]
    omega
  | allocationInstructionAckMessage inner =>
    have bound_inner := AllocationInstructionAckMessage.encode_length_le inner
    simp only [encode]
    omega
  | allocationInstructionAlertMessage inner =>
    have bound_inner := AllocationInstructionAlertMessage.encode_length_le inner
    simp only [encode]
    omega
  | userNotificationMessage inner =>
    simp only [encode, UserNotificationMessage.encode_length]
    omega
  | massCancelClearLockoutRejectMessage inner =>
    simp only [encode, MassCancelClearLockoutRejectMessage.encode_length]
    omega
  | massCancelClearLockoutDoneMessage inner =>
    simp only [encode, MassCancelClearLockoutDoneMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ServerPayload × List UInt8) :=
  if tag = 11 then (ExecutionReportNewMessage.decode bytes).map fun (message, rest) => (.executionReportNewMessage message, rest)
  else if tag = 12 then (ExecutionReportBulkQuotePendingNewMessage.decode bytes).map fun (message, rest) => (.executionReportBulkQuotePendingNewMessage message, rest)
  else if tag = 13 then (ExecutionReportBulkQuoteComponentNewMessage.decode bytes).map fun (message, rest) => (.executionReportBulkQuoteComponentNewMessage message, rest)
  else if tag = 14 then (ExecutionReportRejectedMessage.decode bytes).map fun (message, rest) => (.executionReportRejectedMessage message, rest)
  else if tag = 15 then (ExecutionReportTradeMessage.decode bytes).map fun (message, rest) => (.executionReportTradeMessage message, rest)
  else if tag = 16 then (ExecutionReportPendingCancelMessage.decode bytes).map fun (message, rest) => (.executionReportPendingCancelMessage message, rest)
  else if tag = 17 then (ExecutionReportCanceledMessage.decode bytes).map fun (message, rest) => (.executionReportCanceledMessage message, rest)
  else if tag = 18 then (ExecutionReportPendingReplaceMessage.decode bytes).map fun (message, rest) => (.executionReportPendingReplaceMessage message, rest)
  else if tag = 19 then (ExecutionReportReplacedMessage.decode bytes).map fun (message, rest) => (.executionReportReplacedMessage message, rest)
  else if tag = 20 then (ExecutionReportTradeCorrectionMessage.decode bytes).map fun (message, rest) => (.executionReportTradeCorrectionMessage message, rest)
  else if tag = 21 then (ExecutionReportTradeBreakMessage.decode bytes).map fun (message, rest) => (.executionReportTradeBreakMessage message, rest)
  else if tag = 22 then (ExecutionReportRestatementMessage.decode bytes).map fun (message, rest) => (.executionReportRestatementMessage message, rest)
  else if tag = 23 then (PendingMassCancelMessage.decode bytes).map fun (message, rest) => (.pendingMassCancelMessage message, rest)
  else if tag = 24 then (MassCancelRejectMessage.decode bytes).map fun (message, rest) => (.massCancelRejectMessage message, rest)
  else if tag = 25 then (MassCancelDoneMessage.decode bytes).map fun (message, rest) => (.massCancelDoneMessage message, rest)
  else if tag = 26 then (OrderCancelRejectMessage.decode bytes).map fun (message, rest) => (.orderCancelRejectMessage message, rest)
  else if tag = 27 then (AllocationInstructionAckMessage.decode bytes).map fun (message, rest) => (.allocationInstructionAckMessage message, rest)
  else if tag = 28 then (AllocationInstructionAlertMessage.decode bytes).map fun (message, rest) => (.allocationInstructionAlertMessage message, rest)
  else if tag = 29 then (UserNotificationMessage.decode bytes).map fun (message, rest) => (.userNotificationMessage message, rest)
  else if tag = 30 then (MassCancelClearLockoutRejectMessage.decode bytes).map fun (message, rest) => (.massCancelClearLockoutRejectMessage message, rest)
  else if tag = 31 then (MassCancelClearLockoutDoneMessage.decode bytes).map fun (message, rest) => (.massCancelClearLockoutDoneMessage message, rest)
  else none

@[simp] theorem decode_encode (message : ServerPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ServerPayload

/-- Server Sbe Message -/
structure ServerSbeMessage where
  blockLength : BitVec 16
  schemaId : BitVec 8
  version : BitVec 16
  serverPayload : ServerPayload
  deriving DecidableEq, Repr

namespace ServerSbeMessage

def encode (message : ServerSbeMessage) : List UInt8 :=
  encodeUInt 2 message.blockLength
    ++ (encodeUInt 1 (ServerPayload.tag message.serverPayload)
    ++ (encodeUInt 1 message.schemaId
    ++ (encodeUInt 2 message.version
    ++ (ServerPayload.encode message.serverPayload))))

def decode (bytes : List UInt8) : Option (ServerSbeMessage × List UInt8) := do
  let (blockLength, bytes) ← decodeUInt 2 bytes
  let (templateId, bytes) ← decodeUInt 1 bytes
  let (schemaId, bytes) ← decodeUInt 1 bytes
  let (version, bytes) ← decodeUInt 2 bytes
  let (serverPayload, bytes) ← ServerPayload.decode templateId bytes
  pure ({ blockLength, schemaId, version, serverPayload }, bytes)

theorem encode_length_pos (message : ServerSbeMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ServerSbeMessage) : (encode message).length ≤ 1182514 := by
  unfold encode
  cases message.serverPayload with
  | executionReportNewMessage inner =>
    have bound_inner := ExecutionReportNewMessage.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega
  | executionReportBulkQuotePendingNewMessage inner =>
    have bound_inner := ExecutionReportBulkQuotePendingNewMessage.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega
  | executionReportBulkQuoteComponentNewMessage inner =>
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ExecutionReportBulkQuoteComponentNewMessage.encode_length]
    omega
  | executionReportRejectedMessage inner =>
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ExecutionReportRejectedMessage.encode_length]
    omega
  | executionReportTradeMessage inner =>
    have bound_inner := ExecutionReportTradeMessage.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega
  | executionReportPendingCancelMessage inner =>
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ExecutionReportPendingCancelMessage.encode_length]
    omega
  | executionReportCanceledMessage inner =>
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ExecutionReportCanceledMessage.encode_length]
    omega
  | executionReportPendingReplaceMessage inner =>
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ExecutionReportPendingReplaceMessage.encode_length]
    omega
  | executionReportReplacedMessage inner =>
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ExecutionReportReplacedMessage.encode_length]
    omega
  | executionReportTradeCorrectionMessage inner =>
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ExecutionReportTradeCorrectionMessage.encode_length]
    omega
  | executionReportTradeBreakMessage inner =>
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ExecutionReportTradeBreakMessage.encode_length]
    omega
  | executionReportRestatementMessage inner =>
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ExecutionReportRestatementMessage.encode_length]
    omega
  | pendingMassCancelMessage inner =>
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, PendingMassCancelMessage.encode_length]
    omega
  | massCancelRejectMessage inner =>
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MassCancelRejectMessage.encode_length]
    omega
  | massCancelDoneMessage inner =>
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MassCancelDoneMessage.encode_length]
    omega
  | orderCancelRejectMessage inner =>
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, OrderCancelRejectMessage.encode_length]
    omega
  | allocationInstructionAckMessage inner =>
    have bound_inner := AllocationInstructionAckMessage.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega
  | allocationInstructionAlertMessage inner =>
    have bound_inner := AllocationInstructionAlertMessage.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega
  | userNotificationMessage inner =>
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, UserNotificationMessage.encode_length]
    omega
  | massCancelClearLockoutRejectMessage inner =>
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MassCancelClearLockoutRejectMessage.encode_length]
    omega
  | massCancelClearLockoutDoneMessage inner =>
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MassCancelClearLockoutDoneMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : ServerSbeMessage) (rest : List UInt8) :
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
  rw [ServerPayload.decode_encode, some_bind]
  rfl

end ServerSbeMessage

/-- Sequenced Message -/
structure SequencedMessage where
  serverSbeMessage : ServerSbeMessage
  deriving DecidableEq, Repr

namespace SequencedMessage

def encode (message : SequencedMessage) : List UInt8 :=
  ServerSbeMessage.encode message.serverSbeMessage

def decode (bytes : List UInt8) : Option (SequencedMessage × List UInt8) := do
  let (serverSbeMessage, bytes) ← ServerSbeMessage.decode bytes
  pure ({ serverSbeMessage }, bytes)

theorem encode_length_pos (message : SequencedMessage) : (encode message).length > 0 := by
  have positive := ServerSbeMessage.encode_length_pos message.serverSbeMessage
  unfold encode
  omega

@[simp] theorem decode_encode (message : SequencedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [ServerSbeMessage.decode_encode, some_bind]
  rfl

end SequencedMessage

/-- Any Server Data, selected by Message Type -/
inductive ServerData where
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

namespace ServerData

/-- The Message Type each message is sent under -/
def tag : ServerData → BitVec 8
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

def encode : ServerData → List UInt8
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

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ServerData × List UInt8) :=
  if tag = 1 then (LoginAcceptedMessage.decode bytes).map fun (message, rest) => (.loginAcceptedMessage message, rest)
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

@[simp] theorem decode_encode (message : ServerData) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ServerData

/-- Server Packet -/
structure ServerPacket where
  messageLength : BitVec 16
  serverData : ServerData
  deriving DecidableEq, Repr

namespace ServerPacket

def encode (message : ServerPacket) : List UInt8 :=
  encodeUInt 1 (ServerData.tag message.serverData)
    ++ (encodeUInt 2 message.messageLength
    ++ (ServerData.encode message.serverData))

def decode (bytes : List UInt8) : Option (ServerPacket × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (messageLength, bytes) ← decodeUInt 2 bytes
  let (serverData, bytes) ← ServerData.decode messageType bytes
  pure ({ messageLength, serverData }, bytes)

theorem encode_length_pos (message : ServerPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : ServerPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ServerData.decode_encode, some_bind]
  rfl

end ServerPacket

end Omi.MemxMemxoptionsMemoSbeV15BServer
