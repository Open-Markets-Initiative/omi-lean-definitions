import Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Nordic Pre-Trade Risk Management v1.00.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Sequenced Data Packet is not framed: its length Packet Length is not an integer it reads.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqNordicequitiesRiskcontrolBinaryV1001Server

/-- Reject Reason Code: one byte code -/
def RejectReasonCode.codes : List UInt8 :=
  [0x41, 0x53]

inductive RejectReasonCode where
  | notAuthorized -- Not Authorized
  | sessionNotAvailable -- Session Not Available
  | unlisted (byte : { byte : UInt8 // byte ∉ RejectReasonCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RejectReasonCode

def toByte : RejectReasonCode → UInt8
  | .notAuthorized => 0x41
  | .sessionNotAvailable => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RejectReasonCode :=
  if byte = 0x41 then .notAuthorized
  else .sessionNotAvailable

def ofByte (byte : UInt8) : RejectReasonCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RejectReasonCode) : ofByte value.toByte = value := by
  cases value with
  | notAuthorized => decide
  | sessionNotAvailable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RejectReasonCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RejectReasonCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RejectReasonCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RejectReasonCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RejectReasonCode

/-- Trigger Restrict Symbol On Repeated Order Generation: one byte code -/
def TriggerRestrictSymbolOnRepeatedOrderGeneration.codes : List UInt8 :=
  [0x59, 0x4E, 0x3F]

inductive TriggerRestrictSymbolOnRepeatedOrderGeneration where
  | enabled -- Enabled
  | disabled -- Disabled
  | previousValueKept -- Previous Value Kept
  | unlisted (byte : { byte : UInt8 // byte ∉ TriggerRestrictSymbolOnRepeatedOrderGeneration.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TriggerRestrictSymbolOnRepeatedOrderGeneration

def toByte : TriggerRestrictSymbolOnRepeatedOrderGeneration → UInt8
  | .enabled => 0x59
  | .disabled => 0x4E
  | .previousValueKept => 0x3F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TriggerRestrictSymbolOnRepeatedOrderGeneration :=
  if byte = 0x59 then .enabled
  else if byte = 0x4E then .disabled
  else .previousValueKept

def ofByte (byte : UInt8) : TriggerRestrictSymbolOnRepeatedOrderGeneration :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TriggerRestrictSymbolOnRepeatedOrderGeneration) : ofByte value.toByte = value := by
  cases value with
  | enabled => decide
  | disabled => decide
  | previousValueKept => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TriggerRestrictSymbolOnRepeatedOrderGeneration) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TriggerRestrictSymbolOnRepeatedOrderGeneration × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TriggerRestrictSymbolOnRepeatedOrderGeneration) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TriggerRestrictSymbolOnRepeatedOrderGeneration) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TriggerRestrictSymbolOnRepeatedOrderGeneration

/-- In Auction Market Order Prevention: one byte code -/
def InAuctionMarketOrderPrevention.codes : List UInt8 :=
  [0x59, 0x4E, 0x3F]

inductive InAuctionMarketOrderPrevention where
  | enabled -- Enabled
  | disabled -- Disabled
  | previousValueKept -- Previous Value Kept
  | unlisted (byte : { byte : UInt8 // byte ∉ InAuctionMarketOrderPrevention.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InAuctionMarketOrderPrevention

def toByte : InAuctionMarketOrderPrevention → UInt8
  | .enabled => 0x59
  | .disabled => 0x4E
  | .previousValueKept => 0x3F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InAuctionMarketOrderPrevention :=
  if byte = 0x59 then .enabled
  else if byte = 0x4E then .disabled
  else .previousValueKept

def ofByte (byte : UInt8) : InAuctionMarketOrderPrevention :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InAuctionMarketOrderPrevention) : ofByte value.toByte = value := by
  cases value with
  | enabled => decide
  | disabled => decide
  | previousValueKept => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InAuctionMarketOrderPrevention) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InAuctionMarketOrderPrevention × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InAuctionMarketOrderPrevention) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : InAuctionMarketOrderPrevention) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InAuctionMarketOrderPrevention

/-- In Auction Fat Finger Protection: one byte code -/
def InAuctionFatFingerProtection.codes : List UInt8 :=
  [0x59, 0x4E, 0x3F]

inductive InAuctionFatFingerProtection where
  | enabled -- Enabled
  | disabled -- Disabled
  | previousValueKept -- Previous Value Kept
  | unlisted (byte : { byte : UInt8 // byte ∉ InAuctionFatFingerProtection.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InAuctionFatFingerProtection

def toByte : InAuctionFatFingerProtection → UInt8
  | .enabled => 0x59
  | .disabled => 0x4E
  | .previousValueKept => 0x3F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InAuctionFatFingerProtection :=
  if byte = 0x59 then .enabled
  else if byte = 0x4E then .disabled
  else .previousValueKept

def ofByte (byte : UInt8) : InAuctionFatFingerProtection :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InAuctionFatFingerProtection) : ofByte value.toByte = value := by
  cases value with
  | enabled => decide
  | disabled => decide
  | previousValueKept => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InAuctionFatFingerProtection) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InAuctionFatFingerProtection × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InAuctionFatFingerProtection) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : InAuctionFatFingerProtection) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InAuctionFatFingerProtection

/-- In Auction Market Order Protection: one byte code -/
def InAuctionMarketOrderProtection.codes : List UInt8 :=
  [0x59, 0x4E, 0x3F]

inductive InAuctionMarketOrderProtection where
  | enabled -- Enabled
  | disabled -- Disabled
  | previousValueKept -- Previous Value Kept
  | unlisted (byte : { byte : UInt8 // byte ∉ InAuctionMarketOrderProtection.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InAuctionMarketOrderProtection

def toByte : InAuctionMarketOrderProtection → UInt8
  | .enabled => 0x59
  | .disabled => 0x4E
  | .previousValueKept => 0x3F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InAuctionMarketOrderProtection :=
  if byte = 0x59 then .enabled
  else if byte = 0x4E then .disabled
  else .previousValueKept

def ofByte (byte : UInt8) : InAuctionMarketOrderProtection :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InAuctionMarketOrderProtection) : ofByte value.toByte = value := by
  cases value with
  | enabled => decide
  | disabled => decide
  | previousValueKept => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InAuctionMarketOrderProtection) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InAuctionMarketOrderProtection × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InAuctionMarketOrderProtection) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : InAuctionMarketOrderProtection) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InAuctionMarketOrderProtection

/-- Block And Cancel: one byte code -/
def BlockAndCancel.codes : List UInt8 :=
  [0x42, 0x55, 0x43, 0x3F]

inductive BlockAndCancel where
  | block -- Block
  | unblock -- Unblock
  | blockAndCancel -- Block And Cancel
  | previousValueKept -- Previous Value Kept
  | unlisted (byte : { byte : UInt8 // byte ∉ BlockAndCancel.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BlockAndCancel

def toByte : BlockAndCancel → UInt8
  | .block => 0x42
  | .unblock => 0x55
  | .blockAndCancel => 0x43
  | .previousValueKept => 0x3F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BlockAndCancel :=
  if byte = 0x42 then .block
  else if byte = 0x55 then .unblock
  else if byte = 0x43 then .blockAndCancel
  else .previousValueKept

def ofByte (byte : UInt8) : BlockAndCancel :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BlockAndCancel) : ofByte value.toByte = value := by
  cases value with
  | block => decide
  | unblock => decide
  | blockAndCancel => decide
  | previousValueKept => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BlockAndCancel) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BlockAndCancel × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BlockAndCancel) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : BlockAndCancel) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BlockAndCancel

/-- State: one byte code -/
def State.codes : List UInt8 :=
  [0x41, 0x49, 0x3F]

inductive State where
  | active -- Active
  | inactive -- Inactive
  | previousValueKept -- Previous Value Kept
  | unlisted (byte : { byte : UInt8 // byte ∉ State.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace State

def toByte : State → UInt8
  | .active => 0x41
  | .inactive => 0x49
  | .previousValueKept => 0x3F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : State :=
  if byte = 0x41 then .active
  else if byte = 0x49 then .inactive
  else .previousValueKept

def ofByte (byte : UInt8) : State :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : State) : ofByte value.toByte = value := by
  cases value with
  | active => decide
  | inactive => decide
  | previousValueKept => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : State) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (State × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : State) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : State) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end State

/-- Reject All Flag: one byte code -/
def RejectAllFlag.codes : List UInt8 :=
  [0x59, 0x4E, 0x3F]

inductive RejectAllFlag where
  | enabled -- Enabled
  | disabled -- Disabled
  | previousValueKept -- Previous Value Kept
  | unlisted (byte : { byte : UInt8 // byte ∉ RejectAllFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace RejectAllFlag

def toByte : RejectAllFlag → UInt8
  | .enabled => 0x59
  | .disabled => 0x4E
  | .previousValueKept => 0x3F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : RejectAllFlag :=
  if byte = 0x59 then .enabled
  else if byte = 0x4E then .disabled
  else .previousValueKept

def ofByte (byte : UInt8) : RejectAllFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : RejectAllFlag) : ofByte value.toByte = value := by
  cases value with
  | enabled => decide
  | disabled => decide
  | previousValueKept => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : RejectAllFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (RejectAllFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : RejectAllFlag) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : RejectAllFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end RejectAllFlag

/-- Blow Through Protection: one byte code -/
def BlowThroughProtection.codes : List UInt8 :=
  [0x59, 0x4E, 0x3F]

inductive BlowThroughProtection where
  | enabled -- Enabled
  | disabled -- Disabled
  | previousValueKept -- Previous Value Kept
  | unlisted (byte : { byte : UInt8 // byte ∉ BlowThroughProtection.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BlowThroughProtection

def toByte : BlowThroughProtection → UInt8
  | .enabled => 0x59
  | .disabled => 0x4E
  | .previousValueKept => 0x3F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BlowThroughProtection :=
  if byte = 0x59 then .enabled
  else if byte = 0x4E then .disabled
  else .previousValueKept

def ofByte (byte : UInt8) : BlowThroughProtection :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BlowThroughProtection) : ofByte value.toByte = value := by
  cases value with
  | enabled => decide
  | disabled => decide
  | previousValueKept => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BlowThroughProtection) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BlowThroughProtection × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BlowThroughProtection) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : BlowThroughProtection) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BlowThroughProtection

/-- Reason: one byte code -/
def Reason.codes : List UInt8 :=
  [0x43, 0x41, 0x4E, 0x55]

inductive Reason where
  | invalidCurrency -- Invalid Currency
  | invalidPrmAccount -- Invalid Prm Account
  | noSettingPresent -- No Setting Present
  | unauthorized -- Unauthorized
  | unlisted (byte : { byte : UInt8 // byte ∉ Reason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Reason

def toByte : Reason → UInt8
  | .invalidCurrency => 0x43
  | .invalidPrmAccount => 0x41
  | .noSettingPresent => 0x4E
  | .unauthorized => 0x55
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Reason :=
  if byte = 0x43 then .invalidCurrency
  else if byte = 0x41 then .invalidPrmAccount
  else if byte = 0x4E then .noSettingPresent
  else .unauthorized

def ofByte (byte : UInt8) : Reason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Reason) : ofByte value.toByte = value := by
  cases value with
  | invalidCurrency => decide
  | invalidPrmAccount => decide
  | noSettingPresent => decide
  | unauthorized => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Reason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Reason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Reason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Reason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Reason

/-- Debug Packet: 1 bytes -/
structure DebugPacket where
  debugText : Alpha 1
  deriving DecidableEq, Repr

namespace DebugPacket

def encode (message : DebugPacket) : List UInt8 :=
  Alpha.encode message.debugText

def decode (bytes : List UInt8) : Option (DebugPacket × List UInt8) := do
  let (debugText, bytes) ← Alpha.decode 1 bytes
  pure ({ debugText }, bytes)

@[simp] theorem encode_length (message : DebugPacket) : (encode message).length = 1 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : DebugPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DebugPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end DebugPacket

/-- Login Accepted Packet: 30 bytes -/
structure LoginAcceptedPacket where
  acceptedSession : Alpha 10
  acceptedSequenceNumber : Alpha 20
  deriving DecidableEq, Repr

namespace LoginAcceptedPacket

def encode (message : LoginAcceptedPacket) : List UInt8 :=
  Alpha.encode message.acceptedSession
    ++ (Alpha.encode message.acceptedSequenceNumber)

def decode (bytes : List UInt8) : Option (LoginAcceptedPacket × List UInt8) := do
  let (acceptedSession, bytes) ← Alpha.decode 10 bytes
  let (acceptedSequenceNumber, bytes) ← Alpha.decode 20 bytes
  pure ({ acceptedSession, acceptedSequenceNumber }, bytes)

@[simp] theorem encode_length (message : LoginAcceptedPacket) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : LoginAcceptedPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginAcceptedPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LoginAcceptedPacket

/-- Login Rejected Packet: 1 bytes -/
structure LoginRejectedPacket where
  rejectReasonCode : RejectReasonCode
  deriving DecidableEq, Repr

namespace LoginRejectedPacket

def encode (message : LoginRejectedPacket) : List UInt8 :=
  RejectReasonCode.encode message.rejectReasonCode

def decode (bytes : List UInt8) : Option (LoginRejectedPacket × List UInt8) := do
  let (rejectReasonCode, bytes) ← RejectReasonCode.decode bytes
  pure ({ rejectReasonCode }, bytes)

@[simp] theorem encode_length (message : LoginRejectedPacket) : (encode message).length = 1 := by
  unfold encode
  simp only [RejectReasonCode.encode_length]

theorem encode_length_pos (message : LoginRejectedPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRejectedPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [RejectReasonCode.decode_encode, some_bind]
  rfl

end LoginRejectedPacket

/-- Account Query Response Message: 4 bytes -/
structure AccountQueryResponseMessage where
  userRefNum : BitVec 32
  deriving DecidableEq, Repr

namespace AccountQueryResponseMessage

def encode (message : AccountQueryResponseMessage) : List UInt8 :=
  encodeUInt 4 message.userRefNum

def decode (bytes : List UInt8) : Option (AccountQueryResponseMessage × List UInt8) := do
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  pure ({ userRefNum }, bytes)

@[simp] theorem encode_length (message : AccountQueryResponseMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : AccountQueryResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AccountQueryResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AccountQueryResponseMessage

/-- Account Settings Response Message: 19 bytes -/
structure AccountSettingsResponseMessage where
  userRefNum : BitVec 32
  prmAccount : Alpha 6
  repeatedOrderGeneration : BitVec 32
  triggerRestrictSymbolOnRepeatedOrderGeneration : TriggerRestrictSymbolOnRepeatedOrderGeneration
  inAuctionMarketOrderPrevention : InAuctionMarketOrderPrevention
  inAuctionFatFingerProtection : InAuctionFatFingerProtection
  inAuctionMarketOrderProtection : InAuctionMarketOrderProtection
  blockAndCancel : BlockAndCancel
  deriving DecidableEq, Repr

namespace AccountSettingsResponseMessage

def encode (message : AccountSettingsResponseMessage) : List UInt8 :=
  encodeUInt 4 message.userRefNum
    ++ (Alpha.encode message.prmAccount
    ++ (encodeUInt 4 message.repeatedOrderGeneration
    ++ (TriggerRestrictSymbolOnRepeatedOrderGeneration.encode message.triggerRestrictSymbolOnRepeatedOrderGeneration
    ++ (InAuctionMarketOrderPrevention.encode message.inAuctionMarketOrderPrevention
    ++ (InAuctionFatFingerProtection.encode message.inAuctionFatFingerProtection
    ++ (InAuctionMarketOrderProtection.encode message.inAuctionMarketOrderProtection
    ++ (BlockAndCancel.encode message.blockAndCancel)))))))

def decode (bytes : List UInt8) : Option (AccountSettingsResponseMessage × List UInt8) := do
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (prmAccount, bytes) ← Alpha.decode 6 bytes
  let (repeatedOrderGeneration, bytes) ← decodeUInt 4 bytes
  let (triggerRestrictSymbolOnRepeatedOrderGeneration, bytes) ← TriggerRestrictSymbolOnRepeatedOrderGeneration.decode bytes
  let (inAuctionMarketOrderPrevention, bytes) ← InAuctionMarketOrderPrevention.decode bytes
  let (inAuctionFatFingerProtection, bytes) ← InAuctionFatFingerProtection.decode bytes
  let (inAuctionMarketOrderProtection, bytes) ← InAuctionMarketOrderProtection.decode bytes
  let (blockAndCancel_, bytes) ← BlockAndCancel.decode bytes
  pure ({ userRefNum, prmAccount, repeatedOrderGeneration, triggerRestrictSymbolOnRepeatedOrderGeneration, inAuctionMarketOrderPrevention, inAuctionFatFingerProtection, inAuctionMarketOrderProtection, blockAndCancel := blockAndCancel_ }, bytes)

@[simp] theorem encode_length (message : AccountSettingsResponseMessage) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, TriggerRestrictSymbolOnRepeatedOrderGeneration.encode_length, InAuctionMarketOrderPrevention.encode_length, InAuctionFatFingerProtection.encode_length, InAuctionMarketOrderProtection.encode_length, BlockAndCancel.encode_length]

theorem encode_length_pos (message : AccountSettingsResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AccountSettingsResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TriggerRestrictSymbolOnRepeatedOrderGeneration.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InAuctionMarketOrderPrevention.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InAuctionFatFingerProtection.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InAuctionMarketOrderProtection.decode_encode, some_bind]
  dsimp only
  rw [BlockAndCancel.decode_encode, some_bind]
  rfl

end AccountSettingsResponseMessage

/-- Order Book Restriction Response Message: 23 bytes -/
structure OrderBookRestrictionResponseMessage where
  userRefNum : BitVec 32
  timestamp : BitVec 64
  prmAccount : Alpha 6
  orderBook : BitVec 32
  state : State
  deriving DecidableEq, Repr

namespace OrderBookRestrictionResponseMessage

def encode (message : OrderBookRestrictionResponseMessage) : List UInt8 :=
  encodeUInt 4 message.userRefNum
    ++ (encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.prmAccount
    ++ (encodeUInt 4 message.orderBook
    ++ (State.encode message.state))))

def decode (bytes : List UInt8) : Option (OrderBookRestrictionResponseMessage × List UInt8) := do
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (prmAccount, bytes) ← Alpha.decode 6 bytes
  let (orderBook, bytes) ← decodeUInt 4 bytes
  let (state, bytes) ← State.decode bytes
  pure ({ userRefNum, timestamp, prmAccount, orderBook, state }, bytes)

@[simp] theorem encode_length (message : OrderBookRestrictionResponseMessage) : (encode message).length = 23 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, State.encode_length]

theorem encode_length_pos (message : OrderBookRestrictionResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderBookRestrictionResponseMessage) (rest : List UInt8) :
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
  rw [State.decode_encode, some_bind]
  rfl

end OrderBookRestrictionResponseMessage

/-- Market Segment Restriction Response Message: 21 bytes -/
structure MarketSegmentRestrictionResponseMessage where
  userRefNum : BitVec 32
  timestamp : BitVec 64
  prmAccount : Alpha 6
  marketSegment : BitVec 16
  state : State
  deriving DecidableEq, Repr

namespace MarketSegmentRestrictionResponseMessage

def encode (message : MarketSegmentRestrictionResponseMessage) : List UInt8 :=
  encodeUInt 4 message.userRefNum
    ++ (encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.prmAccount
    ++ (encodeUInt 2 message.marketSegment
    ++ (State.encode message.state))))

def decode (bytes : List UInt8) : Option (MarketSegmentRestrictionResponseMessage × List UInt8) := do
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (prmAccount, bytes) ← Alpha.decode 6 bytes
  let (marketSegment, bytes) ← decodeUInt 2 bytes
  let (state, bytes) ← State.decode bytes
  pure ({ userRefNum, timestamp, prmAccount, marketSegment, state }, bytes)

@[simp] theorem encode_length (message : MarketSegmentRestrictionResponseMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, State.encode_length]

theorem encode_length_pos (message : MarketSegmentRestrictionResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketSegmentRestrictionResponseMessage) (rest : List UInt8) :
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
  rw [State.decode_encode, some_bind]
  rfl

end MarketSegmentRestrictionResponseMessage

/-- Limit Settings Response Message: 109 bytes -/
structure LimitSettingsResponseMessage where
  userRefNum : BitVec 32
  prmAccount : Alpha 6
  currency : Alpha 3
  maxQuantity : BitVec 64
  maxValue : BitVec 64
  unused : BitVec 64
  totalRiskValue : BitVec 64
  tradeBuyValue : BitVec 64
  tradeSellValue : BitVec 64
  tradeNetValue : BitVec 64
  openOrderBuyValue : BitVec 64
  openOrderSellValue : BitVec 64
  openOrderNetValue : BitVec 64
  maxQuantityAuction : BitVec 64
  maxValueAuction : BitVec 64
  deriving DecidableEq, Repr

namespace LimitSettingsResponseMessage

def encode (message : LimitSettingsResponseMessage) : List UInt8 :=
  encodeUInt 4 message.userRefNum
    ++ (Alpha.encode message.prmAccount
    ++ (Alpha.encode message.currency
    ++ (encodeUInt 8 message.maxQuantity
    ++ (encodeUInt 8 message.maxValue
    ++ (encodeUInt 8 message.unused
    ++ (encodeUInt 8 message.totalRiskValue
    ++ (encodeUInt 8 message.tradeBuyValue
    ++ (encodeUInt 8 message.tradeSellValue
    ++ (encodeUInt 8 message.tradeNetValue
    ++ (encodeUInt 8 message.openOrderBuyValue
    ++ (encodeUInt 8 message.openOrderSellValue
    ++ (encodeUInt 8 message.openOrderNetValue
    ++ (encodeUInt 8 message.maxQuantityAuction
    ++ (encodeUInt 8 message.maxValueAuction))))))))))))))

def decode (bytes : List UInt8) : Option (LimitSettingsResponseMessage × List UInt8) := do
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (prmAccount, bytes) ← Alpha.decode 6 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (maxQuantity, bytes) ← decodeUInt 8 bytes
  let (maxValue, bytes) ← decodeUInt 8 bytes
  let (unused, bytes) ← decodeUInt 8 bytes
  let (totalRiskValue, bytes) ← decodeUInt 8 bytes
  let (tradeBuyValue, bytes) ← decodeUInt 8 bytes
  let (tradeSellValue, bytes) ← decodeUInt 8 bytes
  let (tradeNetValue, bytes) ← decodeUInt 8 bytes
  let (openOrderBuyValue, bytes) ← decodeUInt 8 bytes
  let (openOrderSellValue, bytes) ← decodeUInt 8 bytes
  let (openOrderNetValue, bytes) ← decodeUInt 8 bytes
  let (maxQuantityAuction, bytes) ← decodeUInt 8 bytes
  let (maxValueAuction, bytes) ← decodeUInt 8 bytes
  pure ({ userRefNum, prmAccount, currency, maxQuantity, maxValue, unused, totalRiskValue, tradeBuyValue, tradeSellValue, tradeNetValue, openOrderBuyValue, openOrderSellValue, openOrderNetValue, maxQuantityAuction, maxValueAuction }, bytes)

@[simp] theorem encode_length (message : LimitSettingsResponseMessage) : (encode message).length = 109 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : LimitSettingsResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LimitSettingsResponseMessage) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LimitSettingsResponseMessage

/-- Account Currency Setting Response Message: 15 bytes -/
structure AccountCurrencySettingResponseMessage where
  userRefNum : BitVec 32
  prmAccount : Alpha 6
  currency : Alpha 3
  rejectAllFlag : RejectAllFlag
  blowThroughProtection : BlowThroughProtection
  deriving DecidableEq, Repr

namespace AccountCurrencySettingResponseMessage

def encode (message : AccountCurrencySettingResponseMessage) : List UInt8 :=
  encodeUInt 4 message.userRefNum
    ++ (Alpha.encode message.prmAccount
    ++ (Alpha.encode message.currency
    ++ (RejectAllFlag.encode message.rejectAllFlag
    ++ (BlowThroughProtection.encode message.blowThroughProtection))))

def decode (bytes : List UInt8) : Option (AccountCurrencySettingResponseMessage × List UInt8) := do
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (prmAccount, bytes) ← Alpha.decode 6 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (rejectAllFlag, bytes) ← RejectAllFlag.decode bytes
  let (blowThroughProtection, bytes) ← BlowThroughProtection.decode bytes
  pure ({ userRefNum, prmAccount, currency, rejectAllFlag, blowThroughProtection }, bytes)

@[simp] theorem encode_length (message : AccountCurrencySettingResponseMessage) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, RejectAllFlag.encode_length, BlowThroughProtection.encode_length]

theorem encode_length_pos (message : AccountCurrencySettingResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AccountCurrencySettingResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RejectAllFlag.decode_encode, some_bind]
  dsimp only
  rw [BlowThroughProtection.decode_encode, some_bind]
  rfl

end AccountCurrencySettingResponseMessage

/-- Reject Message: 5 bytes -/
structure RejectMessage where
  userRefNum : BitVec 32
  reason : Reason
  deriving DecidableEq, Repr

namespace RejectMessage

def encode (message : RejectMessage) : List UInt8 :=
  encodeUInt 4 message.userRefNum
    ++ (Reason.encode message.reason)

def decode (bytes : List UInt8) : Option (RejectMessage × List UInt8) := do
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (reason, bytes) ← Reason.decode bytes
  pure ({ userRefNum, reason }, bytes)

@[simp] theorem encode_length (message : RejectMessage) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Reason.encode_length]

theorem encode_length_pos (message : RejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Reason.decode_encode, some_bind]
  rfl

end RejectMessage

/-- Api Port Rate Breach Message: 8 bytes -/
structure ApiPortRateBreachMessage where
  timestamp : BitVec 64
  deriving DecidableEq, Repr

namespace ApiPortRateBreachMessage

def encode (message : ApiPortRateBreachMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp

def decode (bytes : List UInt8) : Option (ApiPortRateBreachMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp }, bytes)

@[simp] theorem encode_length (message : ApiPortRateBreachMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : ApiPortRateBreachMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ApiPortRateBreachMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ApiPortRateBreachMessage

/-- Account Rate Breach Message: 15 bytes -/
structure AccountRateBreachMessage where
  timestamp : BitVec 64
  state : State
  prmAccount : Alpha 6
  deriving DecidableEq, Repr

namespace AccountRateBreachMessage

def encode (message : AccountRateBreachMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (State.encode message.state
    ++ (Alpha.encode message.prmAccount))

def decode (bytes : List UInt8) : Option (AccountRateBreachMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (state, bytes) ← State.decode bytes
  let (prmAccount, bytes) ← Alpha.decode 6 bytes
  pure ({ timestamp, state, prmAccount }, bytes)

@[simp] theorem encode_length (message : AccountRateBreachMessage) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, State.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : AccountRateBreachMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AccountRateBreachMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, State.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end AccountRateBreachMessage

/-- Accumulated Values Message: 73 bytes -/
structure AccumulatedValuesMessage where
  prmAccount : Alpha 6
  currency : Alpha 3
  lastUpdateTime : BitVec 64
  riskTotalValue : BitVec 64
  tradesBuyValue : BitVec 64
  tradesSellValue : BitVec 64
  tradesTotalValue : BitVec 64
  ordersBuyValue : BitVec 64
  ordersSellValue : BitVec 64
  ordersTotalValue : BitVec 64
  deriving DecidableEq, Repr

namespace AccumulatedValuesMessage

def encode (message : AccumulatedValuesMessage) : List UInt8 :=
  Alpha.encode message.prmAccount
    ++ (Alpha.encode message.currency
    ++ (encodeUInt 8 message.lastUpdateTime
    ++ (encodeUInt 8 message.riskTotalValue
    ++ (encodeUInt 8 message.tradesBuyValue
    ++ (encodeUInt 8 message.tradesSellValue
    ++ (encodeUInt 8 message.tradesTotalValue
    ++ (encodeUInt 8 message.ordersBuyValue
    ++ (encodeUInt 8 message.ordersSellValue
    ++ (encodeUInt 8 message.ordersTotalValue)))))))))

def decode (bytes : List UInt8) : Option (AccumulatedValuesMessage × List UInt8) := do
  let (prmAccount, bytes) ← Alpha.decode 6 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (lastUpdateTime, bytes) ← decodeUInt 8 bytes
  let (riskTotalValue, bytes) ← decodeUInt 8 bytes
  let (tradesBuyValue, bytes) ← decodeUInt 8 bytes
  let (tradesSellValue, bytes) ← decodeUInt 8 bytes
  let (tradesTotalValue, bytes) ← decodeUInt 8 bytes
  let (ordersBuyValue, bytes) ← decodeUInt 8 bytes
  let (ordersSellValue, bytes) ← decodeUInt 8 bytes
  let (ordersTotalValue, bytes) ← decodeUInt 8 bytes
  pure ({ prmAccount, currency, lastUpdateTime, riskTotalValue, tradesBuyValue, tradesSellValue, tradesTotalValue, ordersBuyValue, ordersSellValue, ordersTotalValue }, bytes)

@[simp] theorem encode_length (message : AccumulatedValuesMessage) : (encode message).length = 73 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : AccumulatedValuesMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AccumulatedValuesMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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

end AccumulatedValuesMessage

/-- Any Sequenced Message, selected by Sequenced Message Type -/
inductive SequencedMessage where
  | accountQueryResponseMessage (message : AccountQueryResponseMessage) -- "Q" 0x51
  | accountSettingsResponseMessage (message : AccountSettingsResponseMessage) -- "C" 0x43
  | orderBookRestrictionResponseMessage (message : OrderBookRestrictionResponseMessage) -- "R" 0x52
  | marketSegmentRestrictionResponseMessage (message : MarketSegmentRestrictionResponseMessage) -- "S" 0x53
  | limitSettingsResponseMessage (message : LimitSettingsResponseMessage) -- "L" 0x4C
  | accountCurrencySettingResponseMessage (message : AccountCurrencySettingResponseMessage) -- "F" 0x46
  | rejectMessage (message : RejectMessage) -- "J" 0x4A
  | apiPortRateBreachMessage (message : ApiPortRateBreachMessage) -- "P" 0x50
  | accountRateBreachMessage (message : AccountRateBreachMessage) -- "B" 0x42
  | accumulatedValuesMessage (message : AccumulatedValuesMessage) -- "V" 0x56
  deriving DecidableEq, Repr

namespace SequencedMessage

/-- The Sequenced Message Type each message is sent under -/
def tag : SequencedMessage → BitVec 8
  | .accountQueryResponseMessage _ => 81
  | .accountSettingsResponseMessage _ => 67
  | .orderBookRestrictionResponseMessage _ => 82
  | .marketSegmentRestrictionResponseMessage _ => 83
  | .limitSettingsResponseMessage _ => 76
  | .accountCurrencySettingResponseMessage _ => 70
  | .rejectMessage _ => 74
  | .apiPortRateBreachMessage _ => 80
  | .accountRateBreachMessage _ => 66
  | .accumulatedValuesMessage _ => 86

def encode : SequencedMessage → List UInt8
  | .accountQueryResponseMessage message => AccountQueryResponseMessage.encode message
  | .accountSettingsResponseMessage message => AccountSettingsResponseMessage.encode message
  | .orderBookRestrictionResponseMessage message => OrderBookRestrictionResponseMessage.encode message
  | .marketSegmentRestrictionResponseMessage message => MarketSegmentRestrictionResponseMessage.encode message
  | .limitSettingsResponseMessage message => LimitSettingsResponseMessage.encode message
  | .accountCurrencySettingResponseMessage message => AccountCurrencySettingResponseMessage.encode message
  | .rejectMessage message => RejectMessage.encode message
  | .apiPortRateBreachMessage message => ApiPortRateBreachMessage.encode message
  | .accountRateBreachMessage message => AccountRateBreachMessage.encode message
  | .accumulatedValuesMessage message => AccumulatedValuesMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SequencedMessage) : (encode message).length ≤ 109 := by
  cases message with
  | accountQueryResponseMessage inner =>
    simp only [encode, AccountQueryResponseMessage.encode_length]
    omega
  | accountSettingsResponseMessage inner =>
    simp only [encode, AccountSettingsResponseMessage.encode_length]
    omega
  | orderBookRestrictionResponseMessage inner =>
    simp only [encode, OrderBookRestrictionResponseMessage.encode_length]
    omega
  | marketSegmentRestrictionResponseMessage inner =>
    simp only [encode, MarketSegmentRestrictionResponseMessage.encode_length]
    omega
  | limitSettingsResponseMessage inner =>
    simp only [encode, LimitSettingsResponseMessage.encode_length]
    omega
  | accountCurrencySettingResponseMessage inner =>
    simp only [encode, AccountCurrencySettingResponseMessage.encode_length]
    omega
  | rejectMessage inner =>
    simp only [encode, RejectMessage.encode_length]
    omega
  | apiPortRateBreachMessage inner =>
    simp only [encode, ApiPortRateBreachMessage.encode_length]
    omega
  | accountRateBreachMessage inner =>
    simp only [encode, AccountRateBreachMessage.encode_length]
    omega
  | accumulatedValuesMessage inner =>
    simp only [encode, AccumulatedValuesMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (SequencedMessage × List UInt8) :=
  if tag = 81 then (AccountQueryResponseMessage.decode bytes).map fun (message, rest) => (.accountQueryResponseMessage message, rest)
  else if tag = 67 then (AccountSettingsResponseMessage.decode bytes).map fun (message, rest) => (.accountSettingsResponseMessage message, rest)
  else if tag = 82 then (OrderBookRestrictionResponseMessage.decode bytes).map fun (message, rest) => (.orderBookRestrictionResponseMessage message, rest)
  else if tag = 83 then (MarketSegmentRestrictionResponseMessage.decode bytes).map fun (message, rest) => (.marketSegmentRestrictionResponseMessage message, rest)
  else if tag = 76 then (LimitSettingsResponseMessage.decode bytes).map fun (message, rest) => (.limitSettingsResponseMessage message, rest)
  else if tag = 70 then (AccountCurrencySettingResponseMessage.decode bytes).map fun (message, rest) => (.accountCurrencySettingResponseMessage message, rest)
  else if tag = 74 then (RejectMessage.decode bytes).map fun (message, rest) => (.rejectMessage message, rest)
  else if tag = 80 then (ApiPortRateBreachMessage.decode bytes).map fun (message, rest) => (.apiPortRateBreachMessage message, rest)
  else if tag = 66 then (AccountRateBreachMessage.decode bytes).map fun (message, rest) => (.accountRateBreachMessage message, rest)
  else if tag = 86 then (AccumulatedValuesMessage.decode bytes).map fun (message, rest) => (.accumulatedValuesMessage message, rest)
  else none

@[simp] theorem decode_encode (message : SequencedMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end SequencedMessage

/-- Sequenced Data Packet -/
structure SequencedDataPacket where
  sequencedMessage : SequencedMessage
  deriving DecidableEq, Repr

namespace SequencedDataPacket

def encode (message : SequencedDataPacket) : List UInt8 :=
  encodeUInt 1 (SequencedMessage.tag message.sequencedMessage)
    ++ (SequencedMessage.encode message.sequencedMessage)

def decode (bytes : List UInt8) : Option (SequencedDataPacket × List UInt8) := do
  let (sequencedMessageType, bytes) ← decodeUInt 1 bytes
  let (sequencedMessage, bytes) ← SequencedMessage.decode sequencedMessageType bytes
  pure ({ sequencedMessage }, bytes)

theorem encode_length_pos (message : SequencedDataPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SequencedDataPacket) : (encode message).length ≤ 110 := by
  unfold encode
  cases message.sequencedMessage with
  | accountQueryResponseMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, AccountQueryResponseMessage.encode_length]
    omega
  | accountSettingsResponseMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, AccountSettingsResponseMessage.encode_length]
    omega
  | orderBookRestrictionResponseMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderBookRestrictionResponseMessage.encode_length]
    omega
  | marketSegmentRestrictionResponseMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, MarketSegmentRestrictionResponseMessage.encode_length]
    omega
  | limitSettingsResponseMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, LimitSettingsResponseMessage.encode_length]
    omega
  | accountCurrencySettingResponseMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, AccountCurrencySettingResponseMessage.encode_length]
    omega
  | rejectMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, RejectMessage.encode_length]
    omega
  | apiPortRateBreachMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, ApiPortRateBreachMessage.encode_length]
    omega
  | accountRateBreachMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, AccountRateBreachMessage.encode_length]
    omega
  | accumulatedValuesMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, AccumulatedValuesMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : SequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SequencedMessage.decode_encode, some_bind]
  rfl

end SequencedDataPacket

/-- Server Heartbeat: 0 bytes -/
structure ServerHeartbeat where
  deriving DecidableEq, Repr

namespace ServerHeartbeat

def encode (_ : ServerHeartbeat) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (ServerHeartbeat × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : ServerHeartbeat) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : ServerHeartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end ServerHeartbeat

/-- End Of Session: 0 bytes -/
structure EndOfSession where
  deriving DecidableEq, Repr

namespace EndOfSession

def encode (_ : EndOfSession) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (EndOfSession × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : EndOfSession) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : EndOfSession) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end EndOfSession

/-- Any Server Payload, selected by Server Packet Type -/
inductive ServerPayload where
  | debugPacket (message : DebugPacket) -- "+" 0x2B
  | loginAcceptedPacket (message : LoginAcceptedPacket) -- "A" 0x41
  | loginRejectedPacket (message : LoginRejectedPacket) -- "J" 0x4A
  | sequencedDataPacket (message : SequencedDataPacket) -- "S" 0x53
  | serverHeartbeat (message : ServerHeartbeat) -- "H" 0x48
  | endOfSession (message : EndOfSession) -- "Z" 0x5A
  deriving DecidableEq, Repr

namespace ServerPayload

/-- The Server Packet Type each message is sent under -/
def tag : ServerPayload → BitVec 8
  | .debugPacket _ => 43
  | .loginAcceptedPacket _ => 65
  | .loginRejectedPacket _ => 74
  | .sequencedDataPacket _ => 83
  | .serverHeartbeat _ => 72
  | .endOfSession _ => 90

def encode : ServerPayload → List UInt8
  | .debugPacket message => DebugPacket.encode message
  | .loginAcceptedPacket message => LoginAcceptedPacket.encode message
  | .loginRejectedPacket message => LoginRejectedPacket.encode message
  | .sequencedDataPacket message => SequencedDataPacket.encode message
  | .serverHeartbeat message => ServerHeartbeat.encode message
  | .endOfSession message => EndOfSession.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ServerPayload) : (encode message).length ≤ 110 := by
  cases message with
  | debugPacket inner =>
    simp only [encode, DebugPacket.encode_length]
    omega
  | loginAcceptedPacket inner =>
    simp only [encode, LoginAcceptedPacket.encode_length]
    omega
  | loginRejectedPacket inner =>
    simp only [encode, LoginRejectedPacket.encode_length]
    omega
  | sequencedDataPacket inner =>
    have bound_inner := SequencedDataPacket.encode_length_le inner
    simp only [encode]
    omega
  | serverHeartbeat inner =>
    simp only [encode, ServerHeartbeat.encode_length]
    omega
  | endOfSession inner =>
    simp only [encode, EndOfSession.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ServerPayload × List UInt8) :=
  if tag = 43 then (DebugPacket.decode bytes).map fun (message, rest) => (.debugPacket message, rest)
  else if tag = 65 then (LoginAcceptedPacket.decode bytes).map fun (message, rest) => (.loginAcceptedPacket message, rest)
  else if tag = 74 then (LoginRejectedPacket.decode bytes).map fun (message, rest) => (.loginRejectedPacket message, rest)
  else if tag = 83 then (SequencedDataPacket.decode bytes).map fun (message, rest) => (.sequencedDataPacket message, rest)
  else if tag = 72 then (ServerHeartbeat.decode bytes).map fun (message, rest) => (.serverHeartbeat message, rest)
  else if tag = 90 then (EndOfSession.decode bytes).map fun (message, rest) => (.endOfSession message, rest)
  else none

@[simp] theorem decode_encode (message : ServerPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ServerPayload

/-- Server Soup Bin Tcp Packet -/
structure ServerSoupBinTcpPacket where
  serverPayload : ServerPayload
  deriving DecidableEq, Repr

namespace ServerSoupBinTcpPacket

def encodeBody (message : ServerSoupBinTcpPacket) : List UInt8 :=
  encodeUInt 1 (ServerPayload.tag message.serverPayload)
    ++ (ServerPayload.encode message.serverPayload)

def decodeBody (bytes : List UInt8) : Option (ServerSoupBinTcpPacket × List UInt8) := do
  let (serverPacketType, bytes) ← decodeUInt 1 bytes
  let (serverPayload, bytes) ← ServerPayload.decode serverPacketType bytes
  pure ({ serverPayload }, bytes)

theorem decodeBody_encodeBody (message : ServerSoupBinTcpPacket) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ServerPayload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : ServerSoupBinTcpPacket) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.serverPayload with
  | debugPacket inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, DebugPacket.encode_length]
    omega
  | loginAcceptedPacket inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, LoginAcceptedPacket.encode_length]
    omega
  | loginRejectedPacket inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, LoginRejectedPacket.encode_length]
    omega
  | sequencedDataPacket inner =>
    have bound_inner := SequencedDataPacket.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length]
    omega
  | serverHeartbeat inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, ServerHeartbeat.encode_length]
    omega
  | endOfSession inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, EndOfSession.encode_length]
    omega

/-- Size rule: Packet Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : ServerSoupBinTcpPacket → List UInt8 :=
  encodeFramed 2 0 encodeBody

def decode : List UInt8 → Option (ServerSoupBinTcpPacket × List UInt8) :=
  decodeFramed 2 0 decodeBody

@[simp] theorem decode_encode (message : ServerSoupBinTcpPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 2 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : ServerSoupBinTcpPacket) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end ServerSoupBinTcpPacket

/-- Server Packet -/
structure ServerPacket where
  serverSoupBinTcpPacket : List ServerSoupBinTcpPacket
  deriving DecidableEq, Repr

namespace ServerPacket

def encode (message : ServerPacket) : List UInt8 :=
  encodeMany ServerSoupBinTcpPacket.encode message.serverSoupBinTcpPacket

def decode (bytes : List UInt8) : Option ServerPacket := do
  let serverSoupBinTcpPacket ← decodeAll ServerSoupBinTcpPacket.decode bytes.length bytes
  pure { serverSoupBinTcpPacket }

theorem decode_encode (message : ServerPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany ServerSoupBinTcpPacket.encode ServerSoupBinTcpPacket.decode ServerSoupBinTcpPacket.decode_encode ServerSoupBinTcpPacket.encode_length_pos message.serverSoupBinTcpPacket _ (encodeMany_length_ge ServerSoupBinTcpPacket.encode ServerSoupBinTcpPacket.encode_length_pos message.serverSoupBinTcpPacket), some_bind]
  rfl

end ServerPacket

end Omi.NasdaqNordicequitiesRiskcontrolBinaryV1001Server
