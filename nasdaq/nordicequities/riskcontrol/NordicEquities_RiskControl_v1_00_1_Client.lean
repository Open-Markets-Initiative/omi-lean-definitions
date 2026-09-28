import Omi.Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Nordic Pre-Trade Risk Management v1.00.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Unsequenced Data Packet is not framed: its length Packet Length is not an integer it reads.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqNordicequitiesRiskcontrolBinaryV1001Client

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

/-- Login Request Packet: 46 bytes -/
structure LoginRequestPacket where
  username : Alpha 6
  password : Alpha 10
  requestedSession : Alpha 10
  requestedSequenceNumber : Alpha 20
  deriving DecidableEq, Repr

namespace LoginRequestPacket

def encode (message : LoginRequestPacket) : List UInt8 :=
  Alpha.encode message.username
    ++ (Alpha.encode message.password
    ++ (Alpha.encode message.requestedSession
    ++ (Alpha.encode message.requestedSequenceNumber)))

def decode (bytes : List UInt8) : Option (LoginRequestPacket × List UInt8) := do
  let (username, bytes) ← Alpha.decode 6 bytes
  let (password, bytes) ← Alpha.decode 10 bytes
  let (requestedSession, bytes) ← Alpha.decode 10 bytes
  let (requestedSequenceNumber, bytes) ← Alpha.decode 20 bytes
  pure ({ username, password, requestedSession, requestedSequenceNumber }, bytes)

@[simp] theorem encode_length (message : LoginRequestPacket) : (encode message).length = 46 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : LoginRequestPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRequestPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LoginRequestPacket

/-- Account Query Message: 0 bytes -/
structure AccountQueryMessage where
  deriving DecidableEq, Repr

namespace AccountQueryMessage

def encode (_ : AccountQueryMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (AccountQueryMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : AccountQueryMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : AccountQueryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end AccountQueryMessage

/-- Modify Account Settings Message: 19 bytes -/
structure ModifyAccountSettingsMessage where
  userRefNum : BitVec 32
  prmAccount : Alpha 6
  repeatedOrderGeneration : BitVec 32
  triggerRestrictSymbolOnRepeatedOrderGeneration : TriggerRestrictSymbolOnRepeatedOrderGeneration
  inAuctionMarketOrderPrevention : InAuctionMarketOrderPrevention
  inAuctionFatFingerProtection : InAuctionFatFingerProtection
  inAuctionMarketOrderProtection : InAuctionMarketOrderProtection
  blockAndCancel : BlockAndCancel
  deriving DecidableEq, Repr

namespace ModifyAccountSettingsMessage

def encode (message : ModifyAccountSettingsMessage) : List UInt8 :=
  encodeUInt 4 message.userRefNum
    ++ (Alpha.encode message.prmAccount
    ++ (encodeUInt 4 message.repeatedOrderGeneration
    ++ (TriggerRestrictSymbolOnRepeatedOrderGeneration.encode message.triggerRestrictSymbolOnRepeatedOrderGeneration
    ++ (InAuctionMarketOrderPrevention.encode message.inAuctionMarketOrderPrevention
    ++ (InAuctionFatFingerProtection.encode message.inAuctionFatFingerProtection
    ++ (InAuctionMarketOrderProtection.encode message.inAuctionMarketOrderProtection
    ++ (BlockAndCancel.encode message.blockAndCancel)))))))

def decode (bytes : List UInt8) : Option (ModifyAccountSettingsMessage × List UInt8) := do
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (prmAccount, bytes) ← Alpha.decode 6 bytes
  let (repeatedOrderGeneration, bytes) ← decodeUInt 4 bytes
  let (triggerRestrictSymbolOnRepeatedOrderGeneration, bytes) ← TriggerRestrictSymbolOnRepeatedOrderGeneration.decode bytes
  let (inAuctionMarketOrderPrevention, bytes) ← InAuctionMarketOrderPrevention.decode bytes
  let (inAuctionFatFingerProtection, bytes) ← InAuctionFatFingerProtection.decode bytes
  let (inAuctionMarketOrderProtection, bytes) ← InAuctionMarketOrderProtection.decode bytes
  let (blockAndCancel_, bytes) ← BlockAndCancel.decode bytes
  pure ({ userRefNum, prmAccount, repeatedOrderGeneration, triggerRestrictSymbolOnRepeatedOrderGeneration, inAuctionMarketOrderPrevention, inAuctionFatFingerProtection, inAuctionMarketOrderProtection, blockAndCancel := blockAndCancel_ }, bytes)

@[simp] theorem encode_length (message : ModifyAccountSettingsMessage) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, TriggerRestrictSymbolOnRepeatedOrderGeneration.encode_length, InAuctionMarketOrderPrevention.encode_length, InAuctionFatFingerProtection.encode_length, InAuctionMarketOrderProtection.encode_length, BlockAndCancel.encode_length]

theorem encode_length_pos (message : ModifyAccountSettingsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ModifyAccountSettingsMessage) (rest : List UInt8) :
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

end ModifyAccountSettingsMessage

/-- Modify Order Book Restriction Message: 15 bytes -/
structure ModifyOrderBookRestrictionMessage where
  userRefNum : BitVec 32
  prmAccount : Alpha 6
  orderBook : BitVec 32
  state : State
  deriving DecidableEq, Repr

namespace ModifyOrderBookRestrictionMessage

def encode (message : ModifyOrderBookRestrictionMessage) : List UInt8 :=
  encodeUInt 4 message.userRefNum
    ++ (Alpha.encode message.prmAccount
    ++ (encodeUInt 4 message.orderBook
    ++ (State.encode message.state)))

def decode (bytes : List UInt8) : Option (ModifyOrderBookRestrictionMessage × List UInt8) := do
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (prmAccount, bytes) ← Alpha.decode 6 bytes
  let (orderBook, bytes) ← decodeUInt 4 bytes
  let (state, bytes) ← State.decode bytes
  pure ({ userRefNum, prmAccount, orderBook, state }, bytes)

@[simp] theorem encode_length (message : ModifyOrderBookRestrictionMessage) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, State.encode_length]

theorem encode_length_pos (message : ModifyOrderBookRestrictionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ModifyOrderBookRestrictionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [State.decode_encode, some_bind]
  rfl

end ModifyOrderBookRestrictionMessage

/-- Modify Market Segment Restriction Message: 13 bytes -/
structure ModifyMarketSegmentRestrictionMessage where
  userRefNum : BitVec 32
  prmAccount : Alpha 6
  marketSegment : BitVec 16
  state : State
  deriving DecidableEq, Repr

namespace ModifyMarketSegmentRestrictionMessage

def encode (message : ModifyMarketSegmentRestrictionMessage) : List UInt8 :=
  encodeUInt 4 message.userRefNum
    ++ (Alpha.encode message.prmAccount
    ++ (encodeUInt 2 message.marketSegment
    ++ (State.encode message.state)))

def decode (bytes : List UInt8) : Option (ModifyMarketSegmentRestrictionMessage × List UInt8) := do
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (prmAccount, bytes) ← Alpha.decode 6 bytes
  let (marketSegment, bytes) ← decodeUInt 2 bytes
  let (state, bytes) ← State.decode bytes
  pure ({ userRefNum, prmAccount, marketSegment, state }, bytes)

@[simp] theorem encode_length (message : ModifyMarketSegmentRestrictionMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, State.encode_length]

theorem encode_length_pos (message : ModifyMarketSegmentRestrictionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ModifyMarketSegmentRestrictionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [State.decode_encode, some_bind]
  rfl

end ModifyMarketSegmentRestrictionMessage

/-- Modify Limit Settings Message: 109 bytes -/
structure ModifyLimitSettingsMessage where
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

namespace ModifyLimitSettingsMessage

def encode (message : ModifyLimitSettingsMessage) : List UInt8 :=
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

def decode (bytes : List UInt8) : Option (ModifyLimitSettingsMessage × List UInt8) := do
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

@[simp] theorem encode_length (message : ModifyLimitSettingsMessage) : (encode message).length = 109 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : ModifyLimitSettingsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ModifyLimitSettingsMessage) (rest : List UInt8) :
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

end ModifyLimitSettingsMessage

/-- Modify Account Currency Setting Message: 15 bytes -/
structure ModifyAccountCurrencySettingMessage where
  userRefNum : BitVec 32
  prmAccount : Alpha 6
  currency : Alpha 3
  rejectAllFlag : RejectAllFlag
  blowThroughProtection : BlowThroughProtection
  deriving DecidableEq, Repr

namespace ModifyAccountCurrencySettingMessage

def encode (message : ModifyAccountCurrencySettingMessage) : List UInt8 :=
  encodeUInt 4 message.userRefNum
    ++ (Alpha.encode message.prmAccount
    ++ (Alpha.encode message.currency
    ++ (RejectAllFlag.encode message.rejectAllFlag
    ++ (BlowThroughProtection.encode message.blowThroughProtection))))

def decode (bytes : List UInt8) : Option (ModifyAccountCurrencySettingMessage × List UInt8) := do
  let (userRefNum, bytes) ← decodeUInt 4 bytes
  let (prmAccount, bytes) ← Alpha.decode 6 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (rejectAllFlag, bytes) ← RejectAllFlag.decode bytes
  let (blowThroughProtection, bytes) ← BlowThroughProtection.decode bytes
  pure ({ userRefNum, prmAccount, currency, rejectAllFlag, blowThroughProtection }, bytes)

@[simp] theorem encode_length (message : ModifyAccountCurrencySettingMessage) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, RejectAllFlag.encode_length, BlowThroughProtection.encode_length]

theorem encode_length_pos (message : ModifyAccountCurrencySettingMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ModifyAccountCurrencySettingMessage) (rest : List UInt8) :
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

end ModifyAccountCurrencySettingMessage

/-- Any Unsequenced Message, selected by Unsequenced Message Type -/
inductive UnsequencedMessage where
  | accountQueryMessage (message : AccountQueryMessage) -- "Q" 0x51
  | modifyAccountSettingsMessage (message : ModifyAccountSettingsMessage) -- "C" 0x43
  | modifyOrderBookRestrictionMessage (message : ModifyOrderBookRestrictionMessage) -- "R" 0x52
  | modifyMarketSegmentRestrictionMessage (message : ModifyMarketSegmentRestrictionMessage) -- "S" 0x53
  | modifyLimitSettingsMessage (message : ModifyLimitSettingsMessage) -- "L" 0x4C
  | modifyAccountCurrencySettingMessage (message : ModifyAccountCurrencySettingMessage) -- "F" 0x46
  deriving DecidableEq, Repr

namespace UnsequencedMessage

/-- The Unsequenced Message Type each message is sent under -/
def tag : UnsequencedMessage → BitVec 8
  | .accountQueryMessage _ => 81
  | .modifyAccountSettingsMessage _ => 67
  | .modifyOrderBookRestrictionMessage _ => 82
  | .modifyMarketSegmentRestrictionMessage _ => 83
  | .modifyLimitSettingsMessage _ => 76
  | .modifyAccountCurrencySettingMessage _ => 70

def encode : UnsequencedMessage → List UInt8
  | .accountQueryMessage message => AccountQueryMessage.encode message
  | .modifyAccountSettingsMessage message => ModifyAccountSettingsMessage.encode message
  | .modifyOrderBookRestrictionMessage message => ModifyOrderBookRestrictionMessage.encode message
  | .modifyMarketSegmentRestrictionMessage message => ModifyMarketSegmentRestrictionMessage.encode message
  | .modifyLimitSettingsMessage message => ModifyLimitSettingsMessage.encode message
  | .modifyAccountCurrencySettingMessage message => ModifyAccountCurrencySettingMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : UnsequencedMessage) : (encode message).length ≤ 109 := by
  cases message with
  | accountQueryMessage inner =>
    simp only [encode, AccountQueryMessage.encode_length]
    omega
  | modifyAccountSettingsMessage inner =>
    simp only [encode, ModifyAccountSettingsMessage.encode_length]
    omega
  | modifyOrderBookRestrictionMessage inner =>
    simp only [encode, ModifyOrderBookRestrictionMessage.encode_length]
    omega
  | modifyMarketSegmentRestrictionMessage inner =>
    simp only [encode, ModifyMarketSegmentRestrictionMessage.encode_length]
    omega
  | modifyLimitSettingsMessage inner =>
    simp only [encode, ModifyLimitSettingsMessage.encode_length]
    omega
  | modifyAccountCurrencySettingMessage inner =>
    simp only [encode, ModifyAccountCurrencySettingMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (UnsequencedMessage × List UInt8) :=
  if tag = 81 then (AccountQueryMessage.decode bytes).map fun (message, rest) => (.accountQueryMessage message, rest)
  else if tag = 67 then (ModifyAccountSettingsMessage.decode bytes).map fun (message, rest) => (.modifyAccountSettingsMessage message, rest)
  else if tag = 82 then (ModifyOrderBookRestrictionMessage.decode bytes).map fun (message, rest) => (.modifyOrderBookRestrictionMessage message, rest)
  else if tag = 83 then (ModifyMarketSegmentRestrictionMessage.decode bytes).map fun (message, rest) => (.modifyMarketSegmentRestrictionMessage message, rest)
  else if tag = 76 then (ModifyLimitSettingsMessage.decode bytes).map fun (message, rest) => (.modifyLimitSettingsMessage message, rest)
  else if tag = 70 then (ModifyAccountCurrencySettingMessage.decode bytes).map fun (message, rest) => (.modifyAccountCurrencySettingMessage message, rest)
  else none

@[simp] theorem decode_encode (message : UnsequencedMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end UnsequencedMessage

/-- Unsequenced Data Packet -/
structure UnsequencedDataPacket where
  unsequencedMessage : UnsequencedMessage
  deriving DecidableEq, Repr

namespace UnsequencedDataPacket

def encode (message : UnsequencedDataPacket) : List UInt8 :=
  encodeUInt 1 (UnsequencedMessage.tag message.unsequencedMessage)
    ++ (UnsequencedMessage.encode message.unsequencedMessage)

def decode (bytes : List UInt8) : Option (UnsequencedDataPacket × List UInt8) := do
  let (unsequencedMessageType, bytes) ← decodeUInt 1 bytes
  let (unsequencedMessage, bytes) ← UnsequencedMessage.decode unsequencedMessageType bytes
  pure ({ unsequencedMessage }, bytes)

theorem encode_length_pos (message : UnsequencedDataPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : UnsequencedDataPacket) : (encode message).length ≤ 110 := by
  unfold encode
  cases message.unsequencedMessage with
  | accountQueryMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, AccountQueryMessage.encode_length]
    omega
  | modifyAccountSettingsMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, ModifyAccountSettingsMessage.encode_length]
    omega
  | modifyOrderBookRestrictionMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, ModifyOrderBookRestrictionMessage.encode_length]
    omega
  | modifyMarketSegmentRestrictionMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, ModifyMarketSegmentRestrictionMessage.encode_length]
    omega
  | modifyLimitSettingsMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, ModifyLimitSettingsMessage.encode_length]
    omega
  | modifyAccountCurrencySettingMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, ModifyAccountCurrencySettingMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : UnsequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [UnsequencedMessage.decode_encode, some_bind]
  rfl

end UnsequencedDataPacket

/-- Client Heartbeat: 0 bytes -/
structure ClientHeartbeat where
  deriving DecidableEq, Repr

namespace ClientHeartbeat

def encode (_ : ClientHeartbeat) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (ClientHeartbeat × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : ClientHeartbeat) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : ClientHeartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end ClientHeartbeat

/-- Logout Request: 0 bytes -/
structure LogoutRequest where
  deriving DecidableEq, Repr

namespace LogoutRequest

def encode (_ : LogoutRequest) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (LogoutRequest × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : LogoutRequest) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : LogoutRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end LogoutRequest

/-- Any Client Payload, selected by Client Packet Type -/
inductive ClientPayload where
  | debugPacket (message : DebugPacket) -- "+" 0x2B
  | loginRequestPacket (message : LoginRequestPacket) -- "L" 0x4C
  | unsequencedDataPacket (message : UnsequencedDataPacket) -- "U" 0x55
  | clientHeartbeat (message : ClientHeartbeat) -- "R" 0x52
  | logoutRequest (message : LogoutRequest) -- "O" 0x4F
  deriving DecidableEq, Repr

namespace ClientPayload

/-- The Client Packet Type each message is sent under -/
def tag : ClientPayload → BitVec 8
  | .debugPacket _ => 43
  | .loginRequestPacket _ => 76
  | .unsequencedDataPacket _ => 85
  | .clientHeartbeat _ => 82
  | .logoutRequest _ => 79

def encode : ClientPayload → List UInt8
  | .debugPacket message => DebugPacket.encode message
  | .loginRequestPacket message => LoginRequestPacket.encode message
  | .unsequencedDataPacket message => UnsequencedDataPacket.encode message
  | .clientHeartbeat message => ClientHeartbeat.encode message
  | .logoutRequest message => LogoutRequest.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ClientPayload) : (encode message).length ≤ 110 := by
  cases message with
  | debugPacket inner =>
    simp only [encode, DebugPacket.encode_length]
    omega
  | loginRequestPacket inner =>
    simp only [encode, LoginRequestPacket.encode_length]
    omega
  | unsequencedDataPacket inner =>
    have bound_inner := UnsequencedDataPacket.encode_length_le inner
    simp only [encode]
    omega
  | clientHeartbeat inner =>
    simp only [encode, ClientHeartbeat.encode_length]
    omega
  | logoutRequest inner =>
    simp only [encode, LogoutRequest.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ClientPayload × List UInt8) :=
  if tag = 43 then (DebugPacket.decode bytes).map fun (message, rest) => (.debugPacket message, rest)
  else if tag = 76 then (LoginRequestPacket.decode bytes).map fun (message, rest) => (.loginRequestPacket message, rest)
  else if tag = 85 then (UnsequencedDataPacket.decode bytes).map fun (message, rest) => (.unsequencedDataPacket message, rest)
  else if tag = 82 then (ClientHeartbeat.decode bytes).map fun (message, rest) => (.clientHeartbeat message, rest)
  else if tag = 79 then (LogoutRequest.decode bytes).map fun (message, rest) => (.logoutRequest message, rest)
  else none

@[simp] theorem decode_encode (message : ClientPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ClientPayload

/-- Client Soup Bin Tcp Packet -/
structure ClientSoupBinTcpPacket where
  clientPayload : ClientPayload
  deriving DecidableEq, Repr

namespace ClientSoupBinTcpPacket

def encodeBody (message : ClientSoupBinTcpPacket) : List UInt8 :=
  encodeUInt 1 (ClientPayload.tag message.clientPayload)
    ++ (ClientPayload.encode message.clientPayload)

def decodeBody (bytes : List UInt8) : Option (ClientSoupBinTcpPacket × List UInt8) := do
  let (clientPacketType, bytes) ← decodeUInt 1 bytes
  let (clientPayload, bytes) ← ClientPayload.decode clientPacketType bytes
  pure ({ clientPayload }, bytes)

theorem decodeBody_encodeBody (message : ClientSoupBinTcpPacket) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ClientPayload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : ClientSoupBinTcpPacket) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.clientPayload with
  | debugPacket inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUInt_length, DebugPacket.encode_length]
    omega
  | loginRequestPacket inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUInt_length, LoginRequestPacket.encode_length]
    omega
  | unsequencedDataPacket inner =>
    have bound_inner := UnsequencedDataPacket.encode_length_le inner
    simp only [ClientPayload.encode, List.length_append, encodeUInt_length]
    omega
  | clientHeartbeat inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUInt_length, ClientHeartbeat.encode_length]
    omega
  | logoutRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUInt_length, LogoutRequest.encode_length]
    omega

/-- Size rule: Packet Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : ClientSoupBinTcpPacket → List UInt8 :=
  encodeFramed 2 0 encodeBody

def decode : List UInt8 → Option (ClientSoupBinTcpPacket × List UInt8) :=
  decodeFramed 2 0 decodeBody

@[simp] theorem decode_encode (message : ClientSoupBinTcpPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 2 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : ClientSoupBinTcpPacket) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end ClientSoupBinTcpPacket

/-- Client Packet -/
structure ClientPacket where
  clientSoupBinTcpPacket : List ClientSoupBinTcpPacket
  deriving DecidableEq, Repr

namespace ClientPacket

def encode (message : ClientPacket) : List UInt8 :=
  encodeMany ClientSoupBinTcpPacket.encode message.clientSoupBinTcpPacket

def decode (bytes : List UInt8) : Option ClientPacket := do
  let clientSoupBinTcpPacket ← decodeAll ClientSoupBinTcpPacket.decode bytes.length bytes
  pure { clientSoupBinTcpPacket }

theorem decode_encode (message : ClientPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany ClientSoupBinTcpPacket.encode ClientSoupBinTcpPacket.decode ClientSoupBinTcpPacket.decode_encode ClientSoupBinTcpPacket.encode_length_pos message.clientSoupBinTcpPacket _ (encodeMany_length_ge ClientSoupBinTcpPacket.encode ClientSoupBinTcpPacket.encode_length_pos message.clientSoupBinTcpPacket), some_bind]
  rfl

end ClientPacket

end Omi.NasdaqNordicequitiesRiskcontrolBinaryV1001Client
