import Wire

/-!
# The Members Exchange Members Orders v1.6.a

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Exec Inst is a bit field set, proven as its 2 byte integer rather than bit by bit.

Note: Mass Cancel Inst is a bit field set, proven as its 1 byte integer rather than bit by bit.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.MemxMemxoptionsMemoSbeV16AClient

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

/-- New Order Single Message -/
structure NewOrderSingleMessage where
  sendingTime : BitVec 64
  clordid : Alpha 20
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
  mtpGroupId : BitVec 16
  matchTradePrevention : BitVec 8
  cancelGroupId : BitVec 16
  riskGroupId : BitVec 16
  partiesGroups : PartiesGroups
  deriving DecidableEq, Repr

namespace NewOrderSingleMessage

def encode (message : NewOrderSingleMessage) : List UInt8 :=
  encodeUInt 8 message.sendingTime
    ++ (Alpha.encode message.clordid
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
    ++ (encodeUInt 2 message.mtpGroupId
    ++ (encodeUInt 1 message.matchTradePrevention
    ++ (encodeUInt 2 message.cancelGroupId
    ++ (encodeUInt 2 message.riskGroupId
    ++ (PartiesGroups.encode message.partiesGroups)))))))))))))))))

def decode (bytes : List UInt8) : Option (NewOrderSingleMessage × List UInt8) := do
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  let (clordid, bytes) ← Alpha.decode 20 bytes
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
  let (mtpGroupId, bytes) ← decodeUInt 2 bytes
  let (matchTradePrevention, bytes) ← decodeUInt 1 bytes
  let (cancelGroupId, bytes) ← decodeUInt 2 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (partiesGroups, bytes) ← PartiesGroups.decode bytes
  pure ({ sendingTime, clordid, securityId, side, orderQty, ordType, priceOptional, timeInForce, positionEffectOptional, execInst, tradingCapacity, repriceFrequency, repriceBehavior, mtpGroupId, matchTradePrevention, cancelGroupId, riskGroupId, partiesGroups }, bytes)

theorem encode_length_pos (message : NewOrderSingleMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : NewOrderSingleMessage) : (encode message).length ≤ 4656 := by
  have bound_partiesGroups := PartiesGroups.encode_length_le message.partiesGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, Side.encode_length, OrdType.encode_length, TimeInForce.encode_length, PositionEffectOptional.encode_length]
  omega

@[simp] theorem decode_encode (message : NewOrderSingleMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [PartiesGroups.decode_encode, some_bind]
  rfl

end NewOrderSingleMessage

/-- Two Sided Quotes Group: 17 bytes -/
structure TwoSidedQuotesGroup where
  listSeqNo : BitVec 8
  securityId : Alpha 8
  bidSize : BitVec 16
  bidPx : BitVec 16
  offerSize : BitVec 16
  offerPx : BitVec 16
  deriving DecidableEq, Repr

namespace TwoSidedQuotesGroup

def encode (message : TwoSidedQuotesGroup) : List UInt8 :=
  encodeUInt 1 message.listSeqNo
    ++ (Alpha.encode message.securityId
    ++ (encodeUInt 2 message.bidSize
    ++ (encodeUInt 2 message.bidPx
    ++ (encodeUInt 2 message.offerSize
    ++ (encodeUInt 2 message.offerPx)))))

def decode (bytes : List UInt8) : Option (TwoSidedQuotesGroup × List UInt8) := do
  let (listSeqNo, bytes) ← decodeUInt 1 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (bidSize, bytes) ← decodeUInt 2 bytes
  let (bidPx, bytes) ← decodeUInt 2 bytes
  let (offerSize, bytes) ← decodeUInt 2 bytes
  let (offerPx, bytes) ← decodeUInt 2 bytes
  pure ({ listSeqNo, securityId, bidSize, bidPx, offerSize, offerPx }, bytes)

@[simp] theorem encode_length (message : TwoSidedQuotesGroup) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : TwoSidedQuotesGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TwoSidedQuotesGroup) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TwoSidedQuotesGroup

/-- Two Sided Quotes Groups -/
structure TwoSidedQuotesGroups where
  blockLengthShort : BitVec 8
  twoSidedQuotesGroup : Bounded 1 TwoSidedQuotesGroup
  deriving DecidableEq, Repr

namespace TwoSidedQuotesGroups

def encode (message : TwoSidedQuotesGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.twoSidedQuotesGroup.val.length)
    ++ (encodeMany TwoSidedQuotesGroup.encode message.twoSidedQuotesGroup.val))

def decode (bytes : List UInt8) : Option (TwoSidedQuotesGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (twoSidedQuotesGroup_, bytes) ← decodeMany TwoSidedQuotesGroup.decode numInGroup.toNat bytes
  if fits_twoSidedQuotesGroup : twoSidedQuotesGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, twoSidedQuotesGroup := ⟨twoSidedQuotesGroup_, fits_twoSidedQuotesGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : TwoSidedQuotesGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TwoSidedQuotesGroups) : (encode message).length ≤ 4337 := by
  have bound_twoSidedQuotesGroup := message.twoSidedQuotesGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const TwoSidedQuotesGroup.encode 17 TwoSidedQuotesGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : TwoSidedQuotesGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 TwoSidedQuotesGroup.encode TwoSidedQuotesGroup.decode TwoSidedQuotesGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.twoSidedQuotesGroup.length_lt]
  rfl

end TwoSidedQuotesGroups

/-- Short Two Sided Bulk Quote Message -/
structure ShortTwoSidedBulkQuoteMessage where
  sendingTime : BitVec 64
  clordid : Alpha 20
  timeInForce : TimeInForce
  execInst : BitVec 16
  tradingCapacity : BitVec 8
  mtpGroupId : BitVec 16
  matchTradePrevention : BitVec 8
  cancelGroupId : BitVec 16
  riskGroupId : BitVec 16
  partiesGroups : PartiesGroups
  twoSidedQuotesGroups : TwoSidedQuotesGroups
  deriving DecidableEq, Repr

namespace ShortTwoSidedBulkQuoteMessage

def encode (message : ShortTwoSidedBulkQuoteMessage) : List UInt8 :=
  encodeUInt 8 message.sendingTime
    ++ (Alpha.encode message.clordid
    ++ (TimeInForce.encode message.timeInForce
    ++ (encodeUInt 2 message.execInst
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 2 message.mtpGroupId
    ++ (encodeUInt 1 message.matchTradePrevention
    ++ (encodeUInt 2 message.cancelGroupId
    ++ (encodeUInt 2 message.riskGroupId
    ++ (PartiesGroups.encode message.partiesGroups
    ++ (TwoSidedQuotesGroups.encode message.twoSidedQuotesGroups))))))))))

def decode (bytes : List UInt8) : Option (ShortTwoSidedBulkQuoteMessage × List UInt8) := do
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (timeInForce, bytes) ← TimeInForce.decode bytes
  let (execInst, bytes) ← decodeUInt 2 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (mtpGroupId, bytes) ← decodeUInt 2 bytes
  let (matchTradePrevention, bytes) ← decodeUInt 1 bytes
  let (cancelGroupId, bytes) ← decodeUInt 2 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (partiesGroups, bytes) ← PartiesGroups.decode bytes
  let (twoSidedQuotesGroups, bytes) ← TwoSidedQuotesGroups.decode bytes
  pure ({ sendingTime, clordid, timeInForce, execInst, tradingCapacity, mtpGroupId, matchTradePrevention, cancelGroupId, riskGroupId, partiesGroups, twoSidedQuotesGroups }, bytes)

theorem encode_length_pos (message : ShortTwoSidedBulkQuoteMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ShortTwoSidedBulkQuoteMessage) : (encode message).length ≤ 8968 := by
  have bound_partiesGroups := PartiesGroups.encode_length_le message.partiesGroups
  have bound_twoSidedQuotesGroups := TwoSidedQuotesGroups.encode_length_le message.twoSidedQuotesGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, TimeInForce.encode_length]
  omega

@[simp] theorem decode_encode (message : ShortTwoSidedBulkQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, PartiesGroups.decode_encode, some_bind]
  dsimp only
  rw [TwoSidedQuotesGroups.decode_encode, some_bind]
  rfl

end ShortTwoSidedBulkQuoteMessage

/-- Long Two Sided Bulk Quote Message -/
structure LongTwoSidedBulkQuoteMessage where
  sendingTime : BitVec 64
  clordid : Alpha 20
  timeInForce : TimeInForce
  execInst : BitVec 16
  tradingCapacity : BitVec 8
  mtpGroupId : BitVec 16
  matchTradePrevention : BitVec 8
  cancelGroupId : BitVec 16
  riskGroupId : BitVec 16
  partiesGroups : PartiesGroups
  twoSidedQuotesGroups : TwoSidedQuotesGroups
  deriving DecidableEq, Repr

namespace LongTwoSidedBulkQuoteMessage

def encode (message : LongTwoSidedBulkQuoteMessage) : List UInt8 :=
  encodeUInt 8 message.sendingTime
    ++ (Alpha.encode message.clordid
    ++ (TimeInForce.encode message.timeInForce
    ++ (encodeUInt 2 message.execInst
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 2 message.mtpGroupId
    ++ (encodeUInt 1 message.matchTradePrevention
    ++ (encodeUInt 2 message.cancelGroupId
    ++ (encodeUInt 2 message.riskGroupId
    ++ (PartiesGroups.encode message.partiesGroups
    ++ (TwoSidedQuotesGroups.encode message.twoSidedQuotesGroups))))))))))

def decode (bytes : List UInt8) : Option (LongTwoSidedBulkQuoteMessage × List UInt8) := do
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (timeInForce, bytes) ← TimeInForce.decode bytes
  let (execInst, bytes) ← decodeUInt 2 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (mtpGroupId, bytes) ← decodeUInt 2 bytes
  let (matchTradePrevention, bytes) ← decodeUInt 1 bytes
  let (cancelGroupId, bytes) ← decodeUInt 2 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (partiesGroups, bytes) ← PartiesGroups.decode bytes
  let (twoSidedQuotesGroups, bytes) ← TwoSidedQuotesGroups.decode bytes
  pure ({ sendingTime, clordid, timeInForce, execInst, tradingCapacity, mtpGroupId, matchTradePrevention, cancelGroupId, riskGroupId, partiesGroups, twoSidedQuotesGroups }, bytes)

theorem encode_length_pos (message : LongTwoSidedBulkQuoteMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LongTwoSidedBulkQuoteMessage) : (encode message).length ≤ 8968 := by
  have bound_partiesGroups := PartiesGroups.encode_length_le message.partiesGroups
  have bound_twoSidedQuotesGroups := TwoSidedQuotesGroups.encode_length_le message.twoSidedQuotesGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, TimeInForce.encode_length]
  omega

@[simp] theorem decode_encode (message : LongTwoSidedBulkQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, PartiesGroups.decode_encode, some_bind]
  dsimp only
  rw [TwoSidedQuotesGroups.decode_encode, some_bind]
  rfl

end LongTwoSidedBulkQuoteMessage

/-- One Sided Quotes Group: 14 bytes -/
structure OneSidedQuotesGroup where
  listSeqNo : BitVec 8
  securityId : Alpha 8
  side : Side
  quantity : BitVec 16
  priceShort : BitVec 16
  deriving DecidableEq, Repr

namespace OneSidedQuotesGroup

def encode (message : OneSidedQuotesGroup) : List UInt8 :=
  encodeUInt 1 message.listSeqNo
    ++ (Alpha.encode message.securityId
    ++ (Side.encode message.side
    ++ (encodeUInt 2 message.quantity
    ++ (encodeUInt 2 message.priceShort))))

def decode (bytes : List UInt8) : Option (OneSidedQuotesGroup × List UInt8) := do
  let (listSeqNo, bytes) ← decodeUInt 1 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (quantity, bytes) ← decodeUInt 2 bytes
  let (priceShort, bytes) ← decodeUInt 2 bytes
  pure ({ listSeqNo, securityId, side, quantity, priceShort }, bytes)

@[simp] theorem encode_length (message : OneSidedQuotesGroup) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, Side.encode_length]

theorem encode_length_pos (message : OneSidedQuotesGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OneSidedQuotesGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OneSidedQuotesGroup

/-- One Sided Quotes Groups -/
structure OneSidedQuotesGroups where
  blockLengthShort : BitVec 8
  oneSidedQuotesGroup : Bounded 1 OneSidedQuotesGroup
  deriving DecidableEq, Repr

namespace OneSidedQuotesGroups

def encode (message : OneSidedQuotesGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.oneSidedQuotesGroup.val.length)
    ++ (encodeMany OneSidedQuotesGroup.encode message.oneSidedQuotesGroup.val))

def decode (bytes : List UInt8) : Option (OneSidedQuotesGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (oneSidedQuotesGroup_, bytes) ← decodeMany OneSidedQuotesGroup.decode numInGroup.toNat bytes
  if fits_oneSidedQuotesGroup : oneSidedQuotesGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, oneSidedQuotesGroup := ⟨oneSidedQuotesGroup_, fits_oneSidedQuotesGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : OneSidedQuotesGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OneSidedQuotesGroups) : (encode message).length ≤ 3572 := by
  have bound_oneSidedQuotesGroup := message.oneSidedQuotesGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const OneSidedQuotesGroup.encode 14 OneSidedQuotesGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : OneSidedQuotesGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 OneSidedQuotesGroup.encode OneSidedQuotesGroup.decode OneSidedQuotesGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.oneSidedQuotesGroup.length_lt]
  rfl

end OneSidedQuotesGroups

/-- Short One Sided Bulk Quote Message -/
structure ShortOneSidedBulkQuoteMessage where
  sendingTime : BitVec 64
  clordid : Alpha 20
  timeInForce : TimeInForce
  execInst : BitVec 16
  tradingCapacity : BitVec 8
  mtpGroupId : BitVec 16
  matchTradePrevention : BitVec 8
  cancelGroupId : BitVec 16
  riskGroupId : BitVec 16
  partiesGroups : PartiesGroups
  oneSidedQuotesGroups : OneSidedQuotesGroups
  deriving DecidableEq, Repr

namespace ShortOneSidedBulkQuoteMessage

def encode (message : ShortOneSidedBulkQuoteMessage) : List UInt8 :=
  encodeUInt 8 message.sendingTime
    ++ (Alpha.encode message.clordid
    ++ (TimeInForce.encode message.timeInForce
    ++ (encodeUInt 2 message.execInst
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 2 message.mtpGroupId
    ++ (encodeUInt 1 message.matchTradePrevention
    ++ (encodeUInt 2 message.cancelGroupId
    ++ (encodeUInt 2 message.riskGroupId
    ++ (PartiesGroups.encode message.partiesGroups
    ++ (OneSidedQuotesGroups.encode message.oneSidedQuotesGroups))))))))))

def decode (bytes : List UInt8) : Option (ShortOneSidedBulkQuoteMessage × List UInt8) := do
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (timeInForce, bytes) ← TimeInForce.decode bytes
  let (execInst, bytes) ← decodeUInt 2 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (mtpGroupId, bytes) ← decodeUInt 2 bytes
  let (matchTradePrevention, bytes) ← decodeUInt 1 bytes
  let (cancelGroupId, bytes) ← decodeUInt 2 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (partiesGroups, bytes) ← PartiesGroups.decode bytes
  let (oneSidedQuotesGroups, bytes) ← OneSidedQuotesGroups.decode bytes
  pure ({ sendingTime, clordid, timeInForce, execInst, tradingCapacity, mtpGroupId, matchTradePrevention, cancelGroupId, riskGroupId, partiesGroups, oneSidedQuotesGroups }, bytes)

theorem encode_length_pos (message : ShortOneSidedBulkQuoteMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ShortOneSidedBulkQuoteMessage) : (encode message).length ≤ 8203 := by
  have bound_partiesGroups := PartiesGroups.encode_length_le message.partiesGroups
  have bound_oneSidedQuotesGroups := OneSidedQuotesGroups.encode_length_le message.oneSidedQuotesGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, TimeInForce.encode_length]
  omega

@[simp] theorem decode_encode (message : ShortOneSidedBulkQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, PartiesGroups.decode_encode, some_bind]
  dsimp only
  rw [OneSidedQuotesGroups.decode_encode, some_bind]
  rfl

end ShortOneSidedBulkQuoteMessage

/-- Long One Sided Bulk Quote Message -/
structure LongOneSidedBulkQuoteMessage where
  sendingTime : BitVec 64
  clordid : Alpha 20
  timeInForce : TimeInForce
  execInst : BitVec 16
  tradingCapacity : BitVec 8
  mtpGroupId : BitVec 16
  matchTradePrevention : BitVec 8
  cancelGroupId : BitVec 16
  riskGroupId : BitVec 16
  partiesGroups : PartiesGroups
  oneSidedQuotesGroups : OneSidedQuotesGroups
  deriving DecidableEq, Repr

namespace LongOneSidedBulkQuoteMessage

def encode (message : LongOneSidedBulkQuoteMessage) : List UInt8 :=
  encodeUInt 8 message.sendingTime
    ++ (Alpha.encode message.clordid
    ++ (TimeInForce.encode message.timeInForce
    ++ (encodeUInt 2 message.execInst
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 2 message.mtpGroupId
    ++ (encodeUInt 1 message.matchTradePrevention
    ++ (encodeUInt 2 message.cancelGroupId
    ++ (encodeUInt 2 message.riskGroupId
    ++ (PartiesGroups.encode message.partiesGroups
    ++ (OneSidedQuotesGroups.encode message.oneSidedQuotesGroups))))))))))

def decode (bytes : List UInt8) : Option (LongOneSidedBulkQuoteMessage × List UInt8) := do
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (timeInForce, bytes) ← TimeInForce.decode bytes
  let (execInst, bytes) ← decodeUInt 2 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (mtpGroupId, bytes) ← decodeUInt 2 bytes
  let (matchTradePrevention, bytes) ← decodeUInt 1 bytes
  let (cancelGroupId, bytes) ← decodeUInt 2 bytes
  let (riskGroupId, bytes) ← decodeUInt 2 bytes
  let (partiesGroups, bytes) ← PartiesGroups.decode bytes
  let (oneSidedQuotesGroups, bytes) ← OneSidedQuotesGroups.decode bytes
  pure ({ sendingTime, clordid, timeInForce, execInst, tradingCapacity, mtpGroupId, matchTradePrevention, cancelGroupId, riskGroupId, partiesGroups, oneSidedQuotesGroups }, bytes)

theorem encode_length_pos (message : LongOneSidedBulkQuoteMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LongOneSidedBulkQuoteMessage) : (encode message).length ≤ 8203 := by
  have bound_partiesGroups := PartiesGroups.encode_length_le message.partiesGroups
  have bound_oneSidedQuotesGroups := OneSidedQuotesGroups.encode_length_le message.oneSidedQuotesGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, TimeInForce.encode_length]
  omega

@[simp] theorem decode_encode (message : LongOneSidedBulkQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, PartiesGroups.decode_encode, some_bind]
  dsimp only
  rw [OneSidedQuotesGroups.decode_encode, some_bind]
  rfl

end LongOneSidedBulkQuoteMessage

/-- Order Cancel Replace Request Message: 79 bytes -/
structure OrderCancelReplaceRequestMessage where
  sendingTime : BitVec 64
  orderIdOptional : BitVec 64
  clordid : Alpha 20
  listSeqNo : BitVec 8
  origclordid : Alpha 20
  securityId : Alpha 8
  side : Side
  orderQty : BitVec 32
  ordType : OrdType
  priceOptional : BitVec 64
  deriving DecidableEq, Repr

namespace OrderCancelReplaceRequestMessage

def encode (message : OrderCancelReplaceRequestMessage) : List UInt8 :=
  encodeUInt 8 message.sendingTime
    ++ (encodeUInt 8 message.orderIdOptional
    ++ (Alpha.encode message.clordid
    ++ (encodeUInt 1 message.listSeqNo
    ++ (Alpha.encode message.origclordid
    ++ (Alpha.encode message.securityId
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.orderQty
    ++ (OrdType.encode message.ordType
    ++ (encodeUInt 8 message.priceOptional)))))))))

def decode (bytes : List UInt8) : Option (OrderCancelReplaceRequestMessage × List UInt8) := do
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  let (orderIdOptional, bytes) ← decodeUInt 8 bytes
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (listSeqNo, bytes) ← decodeUInt 1 bytes
  let (origclordid, bytes) ← Alpha.decode 20 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderQty, bytes) ← decodeUInt 4 bytes
  let (ordType, bytes) ← OrdType.decode bytes
  let (priceOptional, bytes) ← decodeUInt 8 bytes
  pure ({ sendingTime, orderIdOptional, clordid, listSeqNo, origclordid, securityId, side, orderQty, ordType, priceOptional }, bytes)

@[simp] theorem encode_length (message : OrderCancelReplaceRequestMessage) : (encode message).length = 79 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, Side.encode_length, OrdType.encode_length]

theorem encode_length_pos (message : OrderCancelReplaceRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancelReplaceRequestMessage) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderCancelReplaceRequestMessage

/-- Order Cancel Request Message: 66 bytes -/
structure OrderCancelRequestMessage where
  sendingTime : BitVec 64
  orderIdOptional : BitVec 64
  clordid : Alpha 20
  listSeqNo : BitVec 8
  origclordidOptional : Alpha 20
  securityId : Alpha 8
  sideOptional : SideOptional
  deriving DecidableEq, Repr

namespace OrderCancelRequestMessage

def encode (message : OrderCancelRequestMessage) : List UInt8 :=
  encodeUInt 8 message.sendingTime
    ++ (encodeUInt 8 message.orderIdOptional
    ++ (Alpha.encode message.clordid
    ++ (encodeUInt 1 message.listSeqNo
    ++ (Alpha.encode message.origclordidOptional
    ++ (Alpha.encode message.securityId
    ++ (SideOptional.encode message.sideOptional))))))

def decode (bytes : List UInt8) : Option (OrderCancelRequestMessage × List UInt8) := do
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  let (orderIdOptional, bytes) ← decodeUInt 8 bytes
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (listSeqNo, bytes) ← decodeUInt 1 bytes
  let (origclordidOptional, bytes) ← Alpha.decode 20 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (sideOptional, bytes) ← SideOptional.decode bytes
  pure ({ sendingTime, orderIdOptional, clordid, listSeqNo, origclordidOptional, securityId, sideOptional }, bytes)

@[simp] theorem encode_length (message : OrderCancelRequestMessage) : (encode message).length = 66 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, SideOptional.encode_length]

theorem encode_length_pos (message : OrderCancelRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancelRequestMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [SideOptional.decode_encode, some_bind]
  rfl

end OrderCancelRequestMessage

/-- Mass Cancel Request Message: 50 bytes -/
structure MassCancelRequestMessage where
  sendingTime : BitVec 64
  clordid : Alpha 20
  efidOptional : Alpha 4
  underlyingOrSeries : BitVec 8
  underlierOptional : Alpha 6
  optionsSecurityIdOptional : Alpha 8
  cancelGroupId : BitVec 16
  massCancelInst : BitVec 8
  deriving DecidableEq, Repr

namespace MassCancelRequestMessage

def encode (message : MassCancelRequestMessage) : List UInt8 :=
  encodeUInt 8 message.sendingTime
    ++ (Alpha.encode message.clordid
    ++ (Alpha.encode message.efidOptional
    ++ (encodeUInt 1 message.underlyingOrSeries
    ++ (Alpha.encode message.underlierOptional
    ++ (Alpha.encode message.optionsSecurityIdOptional
    ++ (encodeUInt 2 message.cancelGroupId
    ++ (encodeUIntLE 1 message.massCancelInst)))))))

def decode (bytes : List UInt8) : Option (MassCancelRequestMessage × List UInt8) := do
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (efidOptional, bytes) ← Alpha.decode 4 bytes
  let (underlyingOrSeries, bytes) ← decodeUInt 1 bytes
  let (underlierOptional, bytes) ← Alpha.decode 6 bytes
  let (optionsSecurityIdOptional, bytes) ← Alpha.decode 8 bytes
  let (cancelGroupId, bytes) ← decodeUInt 2 bytes
  let (massCancelInst, bytes) ← decodeUIntLE 1 bytes
  pure ({ sendingTime, clordid, efidOptional, underlyingOrSeries, underlierOptional, optionsSecurityIdOptional, cancelGroupId, massCancelInst }, bytes)

@[simp] theorem encode_length (message : MassCancelRequestMessage) : (encode message).length = 50 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : MassCancelRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassCancelRequestMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end MassCancelRequestMessage

/-- Mass Cancel Clear Lockout Request Message: 36 bytes -/
structure MassCancelClearLockoutRequestMessage where
  sendingTime : BitVec 64
  clordid : Alpha 20
  lockoutId : BitVec 64
  deriving DecidableEq, Repr

namespace MassCancelClearLockoutRequestMessage

def encode (message : MassCancelClearLockoutRequestMessage) : List UInt8 :=
  encodeUInt 8 message.sendingTime
    ++ (Alpha.encode message.clordid
    ++ (encodeUInt 8 message.lockoutId))

def decode (bytes : List UInt8) : Option (MassCancelClearLockoutRequestMessage × List UInt8) := do
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  let (clordid, bytes) ← Alpha.decode 20 bytes
  let (lockoutId, bytes) ← decodeUInt 8 bytes
  pure ({ sendingTime, clordid, lockoutId }, bytes)

@[simp] theorem encode_length (message : MassCancelClearLockoutRequestMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : MassCancelClearLockoutRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassCancelClearLockoutRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MassCancelClearLockoutRequestMessage

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

/-- Requested Allocations Group -/
structure RequestedAllocationsGroup where
  allocQty : BitVec 32
  allocPositionEffect : AllocPositionEffect
  nestedPartiesGroups : NestedPartiesGroups
  deriving DecidableEq, Repr

namespace RequestedAllocationsGroup

def encode (message : RequestedAllocationsGroup) : List UInt8 :=
  encodeUInt 4 message.allocQty
    ++ (AllocPositionEffect.encode message.allocPositionEffect
    ++ (NestedPartiesGroups.encode message.nestedPartiesGroups))

def decode (bytes : List UInt8) : Option (RequestedAllocationsGroup × List UInt8) := do
  let (allocQty, bytes) ← decodeUInt 4 bytes
  let (allocPositionEffect, bytes) ← AllocPositionEffect.decode bytes
  let (nestedPartiesGroups, bytes) ← NestedPartiesGroups.decode bytes
  pure ({ allocQty, allocPositionEffect, nestedPartiesGroups }, bytes)

theorem encode_length_pos (message : RequestedAllocationsGroup) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : RequestedAllocationsGroup) : (encode message).length ≤ 4597 := by
  have bound_nestedPartiesGroups := NestedPartiesGroups.encode_length_le message.nestedPartiesGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, AllocPositionEffect.encode_length]
  omega

@[simp] theorem decode_encode (message : RequestedAllocationsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, AllocPositionEffect.decode_encode, some_bind]
  dsimp only
  rw [NestedPartiesGroups.decode_encode, some_bind]
  rfl

end RequestedAllocationsGroup

/-- Requested Allocations Groups -/
structure RequestedAllocationsGroups where
  blockLengthShort : BitVec 8
  requestedAllocationsGroup : Bounded 1 RequestedAllocationsGroup
  deriving DecidableEq, Repr

namespace RequestedAllocationsGroups

def encode (message : RequestedAllocationsGroups) : List UInt8 :=
  encodeUInt 1 message.blockLengthShort
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.requestedAllocationsGroup.val.length)
    ++ (encodeMany RequestedAllocationsGroup.encode message.requestedAllocationsGroup.val))

def decode (bytes : List UInt8) : Option (RequestedAllocationsGroups × List UInt8) := do
  let (blockLengthShort, bytes) ← decodeUInt 1 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (requestedAllocationsGroup_, bytes) ← decodeMany RequestedAllocationsGroup.decode numInGroup.toNat bytes
  if fits_requestedAllocationsGroup : requestedAllocationsGroup_.length < 256 ^ 1 then
    pure ({ blockLengthShort, requestedAllocationsGroup := ⟨requestedAllocationsGroup_, fits_requestedAllocationsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : RequestedAllocationsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : RequestedAllocationsGroups) : (encode message).length ≤ 1172237 := by
  have bound_requestedAllocationsGroup := message.requestedAllocationsGroup.length_lt
  have bound_requestedAllocationsGroup_items := encodeMany_length_le RequestedAllocationsGroup.encode 4597 RequestedAllocationsGroup.encode_length_le message.requestedAllocationsGroup.val
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : RequestedAllocationsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 RequestedAllocationsGroup.encode RequestedAllocationsGroup.decode RequestedAllocationsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.requestedAllocationsGroup.length_lt]
  rfl

end RequestedAllocationsGroups

/-- Allocation Instruction Message -/
structure AllocationInstructionMessage where
  sendingTime : BitVec 64
  allocId : Alpha 20
  allocType : BitVec 8
  allocTransType : BitVec 8
  refAllocIdOptional : Alpha 20
  securityId : Alpha 8
  side : Side
  executionAllocationsGroups : ExecutionAllocationsGroups
  requestedAllocationsGroups : RequestedAllocationsGroups
  deriving DecidableEq, Repr

namespace AllocationInstructionMessage

def encode (message : AllocationInstructionMessage) : List UInt8 :=
  encodeUInt 8 message.sendingTime
    ++ (Alpha.encode message.allocId
    ++ (encodeUInt 1 message.allocType
    ++ (encodeUInt 1 message.allocTransType
    ++ (Alpha.encode message.refAllocIdOptional
    ++ (Alpha.encode message.securityId
    ++ (Side.encode message.side
    ++ (ExecutionAllocationsGroups.encode message.executionAllocationsGroups
    ++ (RequestedAllocationsGroups.encode message.requestedAllocationsGroups))))))))

def decode (bytes : List UInt8) : Option (AllocationInstructionMessage × List UInt8) := do
  let (sendingTime, bytes) ← decodeUInt 8 bytes
  let (allocId, bytes) ← Alpha.decode 20 bytes
  let (allocType, bytes) ← decodeUInt 1 bytes
  let (allocTransType, bytes) ← decodeUInt 1 bytes
  let (refAllocIdOptional, bytes) ← Alpha.decode 20 bytes
  let (securityId, bytes) ← Alpha.decode 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (executionAllocationsGroups, bytes) ← ExecutionAllocationsGroups.decode bytes
  let (requestedAllocationsGroups, bytes) ← RequestedAllocationsGroups.decode bytes
  pure ({ sendingTime, allocId, allocType, allocTransType, refAllocIdOptional, securityId, side, executionAllocationsGroups, requestedAllocationsGroups }, bytes)

theorem encode_length_pos (message : AllocationInstructionMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : AllocationInstructionMessage) : (encode message).length ≤ 1177398 := by
  have bound_executionAllocationsGroups := ExecutionAllocationsGroups.encode_length_le message.executionAllocationsGroups
  have bound_requestedAllocationsGroups := RequestedAllocationsGroups.encode_length_le message.requestedAllocationsGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, Side.encode_length]
  omega

@[simp] theorem decode_encode (message : AllocationInstructionMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecutionAllocationsGroups.decode_encode, some_bind]
  dsimp only
  rw [RequestedAllocationsGroups.decode_encode, some_bind]
  rfl

end AllocationInstructionMessage

/-- Any Client Payload, selected by Template Id -/
inductive ClientPayload where
  | newOrderSingleMessage (message : NewOrderSingleMessage) -- 1
  | shortTwoSidedBulkQuoteMessage (message : ShortTwoSidedBulkQuoteMessage) -- 2
  | longTwoSidedBulkQuoteMessage (message : LongTwoSidedBulkQuoteMessage) -- 3
  | shortOneSidedBulkQuoteMessage (message : ShortOneSidedBulkQuoteMessage) -- 4
  | longOneSidedBulkQuoteMessage (message : LongOneSidedBulkQuoteMessage) -- 5
  | orderCancelReplaceRequestMessage (message : OrderCancelReplaceRequestMessage) -- 6
  | orderCancelRequestMessage (message : OrderCancelRequestMessage) -- 7
  | massCancelRequestMessage (message : MassCancelRequestMessage) -- 8
  | massCancelClearLockoutRequestMessage (message : MassCancelClearLockoutRequestMessage) -- 9
  | allocationInstructionMessage (message : AllocationInstructionMessage) -- 10
  deriving DecidableEq, Repr

namespace ClientPayload

/-- The Template Id each message is sent under -/
def tag : ClientPayload → BitVec 8
  | .newOrderSingleMessage _ => 1
  | .shortTwoSidedBulkQuoteMessage _ => 2
  | .longTwoSidedBulkQuoteMessage _ => 3
  | .shortOneSidedBulkQuoteMessage _ => 4
  | .longOneSidedBulkQuoteMessage _ => 5
  | .orderCancelReplaceRequestMessage _ => 6
  | .orderCancelRequestMessage _ => 7
  | .massCancelRequestMessage _ => 8
  | .massCancelClearLockoutRequestMessage _ => 9
  | .allocationInstructionMessage _ => 10

def encode : ClientPayload → List UInt8
  | .newOrderSingleMessage message => NewOrderSingleMessage.encode message
  | .shortTwoSidedBulkQuoteMessage message => ShortTwoSidedBulkQuoteMessage.encode message
  | .longTwoSidedBulkQuoteMessage message => LongTwoSidedBulkQuoteMessage.encode message
  | .shortOneSidedBulkQuoteMessage message => ShortOneSidedBulkQuoteMessage.encode message
  | .longOneSidedBulkQuoteMessage message => LongOneSidedBulkQuoteMessage.encode message
  | .orderCancelReplaceRequestMessage message => OrderCancelReplaceRequestMessage.encode message
  | .orderCancelRequestMessage message => OrderCancelRequestMessage.encode message
  | .massCancelRequestMessage message => MassCancelRequestMessage.encode message
  | .massCancelClearLockoutRequestMessage message => MassCancelClearLockoutRequestMessage.encode message
  | .allocationInstructionMessage message => AllocationInstructionMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ClientPayload) : (encode message).length ≤ 1177398 := by
  cases message with
  | newOrderSingleMessage inner =>
    have bound_inner := NewOrderSingleMessage.encode_length_le inner
    simp only [encode]
    omega
  | shortTwoSidedBulkQuoteMessage inner =>
    have bound_inner := ShortTwoSidedBulkQuoteMessage.encode_length_le inner
    simp only [encode]
    omega
  | longTwoSidedBulkQuoteMessage inner =>
    have bound_inner := LongTwoSidedBulkQuoteMessage.encode_length_le inner
    simp only [encode]
    omega
  | shortOneSidedBulkQuoteMessage inner =>
    have bound_inner := ShortOneSidedBulkQuoteMessage.encode_length_le inner
    simp only [encode]
    omega
  | longOneSidedBulkQuoteMessage inner =>
    have bound_inner := LongOneSidedBulkQuoteMessage.encode_length_le inner
    simp only [encode]
    omega
  | orderCancelReplaceRequestMessage inner =>
    simp only [encode, OrderCancelReplaceRequestMessage.encode_length]
    omega
  | orderCancelRequestMessage inner =>
    simp only [encode, OrderCancelRequestMessage.encode_length]
    omega
  | massCancelRequestMessage inner =>
    simp only [encode, MassCancelRequestMessage.encode_length]
    omega
  | massCancelClearLockoutRequestMessage inner =>
    simp only [encode, MassCancelClearLockoutRequestMessage.encode_length]
    omega
  | allocationInstructionMessage inner =>
    have bound_inner := AllocationInstructionMessage.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ClientPayload × List UInt8) :=
  if tag = 1 then (NewOrderSingleMessage.decode bytes).map fun (message, rest) => (.newOrderSingleMessage message, rest)
  else if tag = 2 then (ShortTwoSidedBulkQuoteMessage.decode bytes).map fun (message, rest) => (.shortTwoSidedBulkQuoteMessage message, rest)
  else if tag = 3 then (LongTwoSidedBulkQuoteMessage.decode bytes).map fun (message, rest) => (.longTwoSidedBulkQuoteMessage message, rest)
  else if tag = 4 then (ShortOneSidedBulkQuoteMessage.decode bytes).map fun (message, rest) => (.shortOneSidedBulkQuoteMessage message, rest)
  else if tag = 5 then (LongOneSidedBulkQuoteMessage.decode bytes).map fun (message, rest) => (.longOneSidedBulkQuoteMessage message, rest)
  else if tag = 6 then (OrderCancelReplaceRequestMessage.decode bytes).map fun (message, rest) => (.orderCancelReplaceRequestMessage message, rest)
  else if tag = 7 then (OrderCancelRequestMessage.decode bytes).map fun (message, rest) => (.orderCancelRequestMessage message, rest)
  else if tag = 8 then (MassCancelRequestMessage.decode bytes).map fun (message, rest) => (.massCancelRequestMessage message, rest)
  else if tag = 9 then (MassCancelClearLockoutRequestMessage.decode bytes).map fun (message, rest) => (.massCancelClearLockoutRequestMessage message, rest)
  else if tag = 10 then (AllocationInstructionMessage.decode bytes).map fun (message, rest) => (.allocationInstructionMessage message, rest)
  else none

@[simp] theorem decode_encode (message : ClientPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ClientPayload

/-- Client Sbe Message -/
structure ClientSbeMessage where
  blockLength : BitVec 16
  schemaId : BitVec 8
  version : BitVec 16
  clientPayload : ClientPayload
  deriving DecidableEq, Repr

namespace ClientSbeMessage

def encode (message : ClientSbeMessage) : List UInt8 :=
  encodeUInt 2 message.blockLength
    ++ (encodeUInt 1 (ClientPayload.tag message.clientPayload)
    ++ (encodeUInt 1 message.schemaId
    ++ (encodeUInt 2 message.version
    ++ (ClientPayload.encode message.clientPayload))))

def decode (bytes : List UInt8) : Option (ClientSbeMessage × List UInt8) := do
  let (blockLength, bytes) ← decodeUInt 2 bytes
  let (templateId, bytes) ← decodeUInt 1 bytes
  let (schemaId, bytes) ← decodeUInt 1 bytes
  let (version, bytes) ← decodeUInt 2 bytes
  let (clientPayload, bytes) ← ClientPayload.decode templateId bytes
  pure ({ blockLength, schemaId, version, clientPayload }, bytes)

theorem encode_length_pos (message : ClientSbeMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ClientSbeMessage) : (encode message).length ≤ 1177404 := by
  unfold encode
  cases message.clientPayload with
  | newOrderSingleMessage inner =>
    have bound_inner := NewOrderSingleMessage.encode_length_le inner
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega
  | shortTwoSidedBulkQuoteMessage inner =>
    have bound_inner := ShortTwoSidedBulkQuoteMessage.encode_length_le inner
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega
  | longTwoSidedBulkQuoteMessage inner =>
    have bound_inner := LongTwoSidedBulkQuoteMessage.encode_length_le inner
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega
  | shortOneSidedBulkQuoteMessage inner =>
    have bound_inner := ShortOneSidedBulkQuoteMessage.encode_length_le inner
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega
  | longOneSidedBulkQuoteMessage inner =>
    have bound_inner := LongOneSidedBulkQuoteMessage.encode_length_le inner
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega
  | orderCancelReplaceRequestMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, OrderCancelReplaceRequestMessage.encode_length]
    omega
  | orderCancelRequestMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, OrderCancelRequestMessage.encode_length]
    omega
  | massCancelRequestMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MassCancelRequestMessage.encode_length]
    omega
  | massCancelClearLockoutRequestMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, MassCancelClearLockoutRequestMessage.encode_length]
    omega
  | allocationInstructionMessage inner =>
    have bound_inner := AllocationInstructionMessage.encode_length_le inner
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega

@[simp] theorem decode_encode (message : ClientSbeMessage) (rest : List UInt8) :
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
  rw [ClientPayload.decode_encode, some_bind]
  rfl

end ClientSbeMessage

/-- Unsequenced Message -/
structure UnsequencedMessage where
  clientSbeMessage : ClientSbeMessage
  deriving DecidableEq, Repr

namespace UnsequencedMessage

def encode (message : UnsequencedMessage) : List UInt8 :=
  ClientSbeMessage.encode message.clientSbeMessage

def decode (bytes : List UInt8) : Option (UnsequencedMessage × List UInt8) := do
  let (clientSbeMessage, bytes) ← ClientSbeMessage.decode bytes
  pure ({ clientSbeMessage }, bytes)

theorem encode_length_pos (message : UnsequencedMessage) : (encode message).length > 0 := by
  have positive := ClientSbeMessage.encode_length_pos message.clientSbeMessage
  unfold encode
  omega

@[simp] theorem decode_encode (message : UnsequencedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [ClientSbeMessage.decode_encode, some_bind]
  rfl

end UnsequencedMessage

/-- Any Client Data, selected by Message Type -/
inductive ClientData where
  | loginRequestMessage (message : LoginRequestMessage) -- 100
  | replayRequestMessage (message : ReplayRequestMessage) -- 101
  | replayAllRequestMessage (message : ReplayAllRequestMessage) -- 102
  | streamRequestMessage (message : StreamRequestMessage) -- 103
  | unsequencedMessage (message : UnsequencedMessage) -- 104
  deriving DecidableEq, Repr

namespace ClientData

/-- The Message Type each message is sent under -/
def tag : ClientData → BitVec 8
  | .loginRequestMessage _ => 100
  | .replayRequestMessage _ => 101
  | .replayAllRequestMessage _ => 102
  | .streamRequestMessage _ => 103
  | .unsequencedMessage _ => 104

def encode : ClientData → List UInt8
  | .loginRequestMessage message => LoginRequestMessage.encode message
  | .replayRequestMessage message => ReplayRequestMessage.encode message
  | .replayAllRequestMessage message => ReplayAllRequestMessage.encode message
  | .streamRequestMessage message => StreamRequestMessage.encode message
  | .unsequencedMessage message => UnsequencedMessage.encode message

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ClientData × List UInt8) :=
  if tag = 100 then (LoginRequestMessage.decode bytes).map fun (message, rest) => (.loginRequestMessage message, rest)
  else if tag = 101 then (ReplayRequestMessage.decode bytes).map fun (message, rest) => (.replayRequestMessage message, rest)
  else if tag = 102 then (ReplayAllRequestMessage.decode bytes).map fun (message, rest) => (.replayAllRequestMessage message, rest)
  else if tag = 103 then (StreamRequestMessage.decode bytes).map fun (message, rest) => (.streamRequestMessage message, rest)
  else if tag = 104 then (UnsequencedMessage.decode bytes).map fun (message, rest) => (.unsequencedMessage message, rest)
  else none

@[simp] theorem decode_encode (message : ClientData) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ClientData

/-- Client Packet -/
structure ClientPacket where
  messageLength : BitVec 16
  clientData : ClientData
  deriving DecidableEq, Repr

namespace ClientPacket

def encode (message : ClientPacket) : List UInt8 :=
  encodeUInt 1 (ClientData.tag message.clientData)
    ++ (encodeUInt 2 message.messageLength
    ++ (ClientData.encode message.clientData))

def decode (bytes : List UInt8) : Option (ClientPacket × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (messageLength, bytes) ← decodeUInt 2 bytes
  let (clientData, bytes) ← ClientData.decode messageType bytes
  pure ({ messageLength, clientData }, bytes)

theorem encode_length_pos (message : ClientPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : ClientPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ClientData.decode_encode, some_bind]
  rfl

end ClientPacket

end Omi.MemxMemxoptionsMemoSbeV16AClient
