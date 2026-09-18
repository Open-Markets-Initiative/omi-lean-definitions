import Omi.Wire

/-!
# Australian Securities Exchange Asx Trade v3.6

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Match Attributes is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Sequenced Data Packet is not framed: its length Packet Length is not an integer it reads.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.AsxAsxsecuritiesTradeOuchV36Server

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x42, 0x53, 0x54, 0x43]

inductive Side where
  | buyOrder -- Buy Order
  | sellOrder -- Sell Order
  | shortSellOrder -- Short Sell Order
  | combinationBuyOrder -- Combination Buy Order
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buyOrder => 0x42
  | .sellOrder => 0x53
  | .shortSellOrder => 0x54
  | .combinationBuyOrder => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x42 then .buyOrder
  else if byte = 0x53 then .sellOrder
  else if byte = 0x54 then .shortSellOrder
  else .combinationBuyOrder

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buyOrder => decide
  | sellOrder => decide
  | shortSellOrder => decide
  | combinationBuyOrder => decide
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

/-- Capacity Of Participant: one byte code -/
def CapacityOfParticipant.codes : List UInt8 :=
  [0x41, 0x50, 0x4D]

inductive CapacityOfParticipant where
  | agency -- Agency
  | principal -- Principal
  | mixed -- Mixed
  | unlisted (byte : { byte : UInt8 // byte ∉ CapacityOfParticipant.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CapacityOfParticipant

def toByte : CapacityOfParticipant → UInt8
  | .agency => 0x41
  | .principal => 0x50
  | .mixed => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CapacityOfParticipant :=
  if byte = 0x41 then .agency
  else if byte = 0x50 then .principal
  else .mixed

def ofByte (byte : UInt8) : CapacityOfParticipant :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CapacityOfParticipant) : ofByte value.toByte = value := by
  cases value with
  | agency => decide
  | principal => decide
  | mixed => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CapacityOfParticipant) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CapacityOfParticipant × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CapacityOfParticipant) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CapacityOfParticipant) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CapacityOfParticipant

/-- Directed Wholesale: one byte code -/
def DirectedWholesale.codes : List UInt8 :=
  [0x59, 0x4E]

inductive DirectedWholesale where
  | true_ -- True
  | false_ -- False
  | unlisted (byte : { byte : UInt8 // byte ∉ DirectedWholesale.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DirectedWholesale

def toByte : DirectedWholesale → UInt8
  | .true_ => 0x59
  | .false_ => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DirectedWholesale :=
  if byte = 0x59 then .true_
  else .false_

def ofByte (byte : UInt8) : DirectedWholesale :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DirectedWholesale) : ofByte value.toByte = value := by
  cases value with
  | true_ => decide
  | false_ => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : DirectedWholesale) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (DirectedWholesale × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : DirectedWholesale) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : DirectedWholesale) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end DirectedWholesale

/-- Ouch Order Type: one byte code -/
def OuchOrderType.codes : List UInt8 :=
  [0x59, 0x4E, 0x44, 0x53, 0x50, 0x42, 0x46, 0x54, 0x43, 0x45]

inductive OuchOrderType where
  | limitOrder -- Limit Order
  | centrePointOrder -- Centre Point Order
  | centrePointOrder_44 -- Centre Point Order
  | sweepOrder -- Sweep Order
  | dualpostedSweepOrder -- Dualposted Sweep Order
  | centrePointBlockOrderWithSingleFillMaq -- Centre Point Block Order With Single Fill Maq
  | centrePointOrderWithSingleFillMaq -- Centre Point Order With Single Fill Maq
  | limitSweepOrderWithSingleFillMaq -- Limit Sweep Order With Single Fill Maq
  | anyPriceBlockOrder -- Any Price Block Order
  | anyPriceBlockOrderWithSingleFillMaq -- Any Price Block Order With Single Fill Maq
  | unlisted (byte : { byte : UInt8 // byte ∉ OuchOrderType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OuchOrderType

def toByte : OuchOrderType → UInt8
  | .limitOrder => 0x59
  | .centrePointOrder => 0x4E
  | .centrePointOrder_44 => 0x44
  | .sweepOrder => 0x53
  | .dualpostedSweepOrder => 0x50
  | .centrePointBlockOrderWithSingleFillMaq => 0x42
  | .centrePointOrderWithSingleFillMaq => 0x46
  | .limitSweepOrderWithSingleFillMaq => 0x54
  | .anyPriceBlockOrder => 0x43
  | .anyPriceBlockOrderWithSingleFillMaq => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OuchOrderType :=
  if byte = 0x59 then .limitOrder
  else if byte = 0x4E then .centrePointOrder
  else if byte = 0x44 then .centrePointOrder_44
  else if byte = 0x53 then .sweepOrder
  else if byte = 0x50 then .dualpostedSweepOrder
  else if byte = 0x42 then .centrePointBlockOrderWithSingleFillMaq
  else if byte = 0x46 then .centrePointOrderWithSingleFillMaq
  else if byte = 0x54 then .limitSweepOrderWithSingleFillMaq
  else if byte = 0x43 then .anyPriceBlockOrder
  else .anyPriceBlockOrderWithSingleFillMaq

def ofByte (byte : UInt8) : OuchOrderType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OuchOrderType) : ofByte value.toByte = value := by
  cases value with
  | limitOrder => decide
  | centrePointOrder => decide
  | centrePointOrder_44 => decide
  | sweepOrder => decide
  | dualpostedSweepOrder => decide
  | centrePointBlockOrderWithSingleFillMaq => decide
  | centrePointOrderWithSingleFillMaq => decide
  | limitSweepOrderWithSingleFillMaq => decide
  | anyPriceBlockOrder => decide
  | anyPriceBlockOrderWithSingleFillMaq => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OuchOrderType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OuchOrderType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OuchOrderType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OuchOrderType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OuchOrderType

/-- Debug Packet: 1 bytes -/
structure DebugPacket where
  text : Alpha 1
  deriving DecidableEq, Repr

namespace DebugPacket

def encode (message : DebugPacket) : List UInt8 :=
  Alpha.encode message.text

def decode (bytes : List UInt8) : Option (DebugPacket × List UInt8) := do
  let (text, bytes) ← Alpha.decode 1 bytes
  pure ({ text }, bytes)

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
  session : Alpha 10
  sequenceNumber : Alpha 20
  deriving DecidableEq, Repr

namespace LoginAcceptedPacket

def encode (message : LoginAcceptedPacket) : List UInt8 :=
  Alpha.encode message.session
    ++ (Alpha.encode message.sequenceNumber)

def decode (bytes : List UInt8) : Option (LoginAcceptedPacket × List UInt8) := do
  let (session, bytes) ← Alpha.decode 10 bytes
  let (sequenceNumber, bytes) ← Alpha.decode 20 bytes
  pure ({ session, sequenceNumber }, bytes)

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
  rejectReasonCode : Alpha 1
  deriving DecidableEq, Repr

namespace LoginRejectedPacket

def encode (message : LoginRejectedPacket) : List UInt8 :=
  Alpha.encode message.rejectReasonCode

def decode (bytes : List UInt8) : Option (LoginRejectedPacket × List UInt8) := do
  let (rejectReasonCode, bytes) ← Alpha.decode 1 bytes
  pure ({ rejectReasonCode }, bytes)

@[simp] theorem encode_length (message : LoginRejectedPacket) : (encode message).length = 1 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : LoginRejectedPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRejectedPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end LoginRejectedPacket

/-- Regulatory Data: 44 bytes -/
structure RegulatoryData where
  capacityOfParticipant : CapacityOfParticipant
  directedWholesale : DirectedWholesale
  executionVenue : Alpha 4
  intermediaryId : Alpha 10
  orderOrigin : Alpha 20
  filler : Alpha 8
  deriving DecidableEq, Repr

namespace RegulatoryData

def encode (message : RegulatoryData) : List UInt8 :=
  CapacityOfParticipant.encode message.capacityOfParticipant
    ++ (DirectedWholesale.encode message.directedWholesale
    ++ (Alpha.encode message.executionVenue
    ++ (Alpha.encode message.intermediaryId
    ++ (Alpha.encode message.orderOrigin
    ++ (Alpha.encode message.filler)))))

def decode (bytes : List UInt8) : Option (RegulatoryData × List UInt8) := do
  let (capacityOfParticipant, bytes) ← CapacityOfParticipant.decode bytes
  let (directedWholesale, bytes) ← DirectedWholesale.decode bytes
  let (executionVenue, bytes) ← Alpha.decode 4 bytes
  let (intermediaryId, bytes) ← Alpha.decode 10 bytes
  let (orderOrigin, bytes) ← Alpha.decode 20 bytes
  let (filler, bytes) ← Alpha.decode 8 bytes
  pure ({ capacityOfParticipant, directedWholesale, executionVenue, intermediaryId, orderOrigin, filler }, bytes)

@[simp] theorem encode_length (message : RegulatoryData) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, CapacityOfParticipant.encode_length, DirectedWholesale.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : RegulatoryData) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RegulatoryData) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, CapacityOfParticipant.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, DirectedWholesale.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RegulatoryData

/-- Order Accepted Message: 173 bytes -/
structure OrderAcceptedMessage where
  timestampNanoseconds : BitVec 64
  orderToken : Alpha 14
  orderBookId : BitVec 32
  side : Side
  orderId : BitVec 64
  quantity : BitVec 64
  price : BitVec 32
  timeInForce : BitVec 8
  openClose : BitVec 8
  clientAccount : Alpha 10
  orderState : BitVec 8
  customerInfo : Alpha 15
  exchangeInfo : Alpha 32
  clearingParticipant : Alpha 1
  crossingKey : BitVec 32
  regulatoryData : RegulatoryData
  ouchOrderType : OuchOrderType
  shortSellQuantity : BitVec 64
  minimumAcceptableQuantity : BitVec 64
  deriving DecidableEq, Repr

namespace OrderAcceptedMessage

def encode (message : OrderAcceptedMessage) : List UInt8 :=
  encodeUInt 8 message.timestampNanoseconds
    ++ (Alpha.encode message.orderToken
    ++ (encodeUInt 4 message.orderBookId
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.orderId
    ++ (encodeUInt 8 message.quantity
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 1 message.timeInForce
    ++ (encodeUInt 1 message.openClose
    ++ (Alpha.encode message.clientAccount
    ++ (encodeUInt 1 message.orderState
    ++ (Alpha.encode message.customerInfo
    ++ (Alpha.encode message.exchangeInfo
    ++ (Alpha.encode message.clearingParticipant
    ++ (encodeUInt 4 message.crossingKey
    ++ (RegulatoryData.encode message.regulatoryData
    ++ (OuchOrderType.encode message.ouchOrderType
    ++ (encodeUInt 8 message.shortSellQuantity
    ++ (encodeUInt 8 message.minimumAcceptableQuantity))))))))))))))))))

def decode (bytes : List UInt8) : Option (OrderAcceptedMessage × List UInt8) := do
  let (timestampNanoseconds, bytes) ← decodeUInt 8 bytes
  let (orderToken, bytes) ← Alpha.decode 14 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (quantity, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (openClose, bytes) ← decodeUInt 1 bytes
  let (clientAccount, bytes) ← Alpha.decode 10 bytes
  let (orderState, bytes) ← decodeUInt 1 bytes
  let (customerInfo, bytes) ← Alpha.decode 15 bytes
  let (exchangeInfo, bytes) ← Alpha.decode 32 bytes
  let (clearingParticipant, bytes) ← Alpha.decode 1 bytes
  let (crossingKey, bytes) ← decodeUInt 4 bytes
  let (regulatoryData, bytes) ← RegulatoryData.decode bytes
  let (ouchOrderType, bytes) ← OuchOrderType.decode bytes
  let (shortSellQuantity, bytes) ← decodeUInt 8 bytes
  let (minimumAcceptableQuantity, bytes) ← decodeUInt 8 bytes
  pure ({ timestampNanoseconds, orderToken, orderBookId, side, orderId, quantity, price, timeInForce, openClose, clientAccount, orderState, customerInfo, exchangeInfo, clearingParticipant, crossingKey, regulatoryData, ouchOrderType, shortSellQuantity, minimumAcceptableQuantity }, bytes)

@[simp] theorem encode_length (message : OrderAcceptedMessage) : (encode message).length = 173 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, Side.encode_length, RegulatoryData.encode_length, OuchOrderType.encode_length]

theorem encode_length_pos (message : OrderAcceptedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderAcceptedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, RegulatoryData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OuchOrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderAcceptedMessage

/-- Order Rejected Message: 26 bytes -/
structure OrderRejectedMessage where
  timestampNanoseconds : BitVec 64
  orderToken : Alpha 14
  rejectCode : BitVec 32
  deriving DecidableEq, Repr

namespace OrderRejectedMessage

def encode (message : OrderRejectedMessage) : List UInt8 :=
  encodeUInt 8 message.timestampNanoseconds
    ++ (Alpha.encode message.orderToken
    ++ (encodeUInt 4 message.rejectCode))

def decode (bytes : List UInt8) : Option (OrderRejectedMessage × List UInt8) := do
  let (timestampNanoseconds, bytes) ← decodeUInt 8 bytes
  let (orderToken, bytes) ← Alpha.decode 14 bytes
  let (rejectCode, bytes) ← decodeUInt 4 bytes
  pure ({ timestampNanoseconds, orderToken, rejectCode }, bytes)

@[simp] theorem encode_length (message : OrderRejectedMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderRejectedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderRejectedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderRejectedMessage

/-- Order Replaced Message: 187 bytes -/
structure OrderReplacedMessage where
  timestampNanoseconds : BitVec 64
  replacementOrderToken : Alpha 14
  previousOrderToken : Alpha 14
  orderBookId : BitVec 32
  side : Side
  orderId : BitVec 64
  quantity : BitVec 64
  price : BitVec 32
  timeInForce : BitVec 8
  openClose : BitVec 8
  clientAccount : Alpha 10
  orderState : BitVec 8
  customerInfo : Alpha 15
  exchangeInfo : Alpha 32
  clearingParticipant : Alpha 1
  crossingKey : BitVec 32
  regulatoryData : RegulatoryData
  ouchOrderType : OuchOrderType
  shortSellQuantity : BitVec 64
  minimumAcceptableQuantity : BitVec 64
  deriving DecidableEq, Repr

namespace OrderReplacedMessage

def encode (message : OrderReplacedMessage) : List UInt8 :=
  encodeUInt 8 message.timestampNanoseconds
    ++ (Alpha.encode message.replacementOrderToken
    ++ (Alpha.encode message.previousOrderToken
    ++ (encodeUInt 4 message.orderBookId
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.orderId
    ++ (encodeUInt 8 message.quantity
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 1 message.timeInForce
    ++ (encodeUInt 1 message.openClose
    ++ (Alpha.encode message.clientAccount
    ++ (encodeUInt 1 message.orderState
    ++ (Alpha.encode message.customerInfo
    ++ (Alpha.encode message.exchangeInfo
    ++ (Alpha.encode message.clearingParticipant
    ++ (encodeUInt 4 message.crossingKey
    ++ (RegulatoryData.encode message.regulatoryData
    ++ (OuchOrderType.encode message.ouchOrderType
    ++ (encodeUInt 8 message.shortSellQuantity
    ++ (encodeUInt 8 message.minimumAcceptableQuantity)))))))))))))))))))

def decode (bytes : List UInt8) : Option (OrderReplacedMessage × List UInt8) := do
  let (timestampNanoseconds, bytes) ← decodeUInt 8 bytes
  let (replacementOrderToken, bytes) ← Alpha.decode 14 bytes
  let (previousOrderToken, bytes) ← Alpha.decode 14 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (quantity, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (openClose, bytes) ← decodeUInt 1 bytes
  let (clientAccount, bytes) ← Alpha.decode 10 bytes
  let (orderState, bytes) ← decodeUInt 1 bytes
  let (customerInfo, bytes) ← Alpha.decode 15 bytes
  let (exchangeInfo, bytes) ← Alpha.decode 32 bytes
  let (clearingParticipant, bytes) ← Alpha.decode 1 bytes
  let (crossingKey, bytes) ← decodeUInt 4 bytes
  let (regulatoryData, bytes) ← RegulatoryData.decode bytes
  let (ouchOrderType, bytes) ← OuchOrderType.decode bytes
  let (shortSellQuantity, bytes) ← decodeUInt 8 bytes
  let (minimumAcceptableQuantity, bytes) ← decodeUInt 8 bytes
  pure ({ timestampNanoseconds, replacementOrderToken, previousOrderToken, orderBookId, side, orderId, quantity, price, timeInForce, openClose, clientAccount, orderState, customerInfo, exchangeInfo, clearingParticipant, crossingKey, regulatoryData, ouchOrderType, shortSellQuantity, minimumAcceptableQuantity }, bytes)

@[simp] theorem encode_length (message : OrderReplacedMessage) : (encode message).length = 187 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, Side.encode_length, RegulatoryData.encode_length, OuchOrderType.encode_length]

theorem encode_length_pos (message : OrderReplacedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderReplacedMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, RegulatoryData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OuchOrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderReplacedMessage

/-- Order Cancelled Message: 36 bytes -/
structure OrderCancelledMessage where
  timestampNanoseconds : BitVec 64
  orderToken : Alpha 14
  orderBookId : BitVec 32
  side : Side
  orderId : BitVec 64
  reason : BitVec 8
  deriving DecidableEq, Repr

namespace OrderCancelledMessage

def encode (message : OrderCancelledMessage) : List UInt8 :=
  encodeUInt 8 message.timestampNanoseconds
    ++ (Alpha.encode message.orderToken
    ++ (encodeUInt 4 message.orderBookId
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.orderId
    ++ (encodeUInt 1 message.reason)))))

def decode (bytes : List UInt8) : Option (OrderCancelledMessage × List UInt8) := do
  let (timestampNanoseconds, bytes) ← decodeUInt 8 bytes
  let (orderToken, bytes) ← Alpha.decode 14 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (reason, bytes) ← decodeUInt 1 bytes
  pure ({ timestampNanoseconds, orderToken, orderBookId, side, orderId, reason }, bytes)

@[simp] theorem encode_length (message : OrderCancelledMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, Side.encode_length]

theorem encode_length_pos (message : OrderCancelledMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancelledMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderCancelledMessage

/-- Order Executed Message: 53 bytes -/
structure OrderExecutedMessage where
  timestampNanoseconds : BitVec 64
  orderToken : Alpha 14
  orderBookId : BitVec 32
  tradedQuantity : BitVec 64
  tradePrice : BitVec 32
  matchId : BitVec 96
  dealSource : BitVec 16
  matchAttributes : BitVec 8
  deriving DecidableEq, Repr

namespace OrderExecutedMessage

def encode (message : OrderExecutedMessage) : List UInt8 :=
  encodeUInt 8 message.timestampNanoseconds
    ++ (Alpha.encode message.orderToken
    ++ (encodeUInt 4 message.orderBookId
    ++ (encodeUInt 8 message.tradedQuantity
    ++ (encodeUInt 4 message.tradePrice
    ++ (encodeUInt 12 message.matchId
    ++ (encodeUInt 2 message.dealSource
    ++ (encodeUInt 1 message.matchAttributes)))))))

def decode (bytes : List UInt8) : Option (OrderExecutedMessage × List UInt8) := do
  let (timestampNanoseconds, bytes) ← decodeUInt 8 bytes
  let (orderToken, bytes) ← Alpha.decode 14 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (tradedQuantity, bytes) ← decodeUInt 8 bytes
  let (tradePrice, bytes) ← decodeUInt 4 bytes
  let (matchId, bytes) ← decodeUInt 12 bytes
  let (dealSource, bytes) ← decodeUInt 2 bytes
  let (matchAttributes, bytes) ← decodeUInt 1 bytes
  pure ({ timestampNanoseconds, orderToken, orderBookId, tradedQuantity, tradePrice, matchId, dealSource, matchAttributes }, bytes)

@[simp] theorem encode_length (message : OrderExecutedMessage) : (encode message).length = 53 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderExecutedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecutedMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderExecutedMessage

/-- Any Sequenced Message, selected by Sequenced Message Type -/
inductive SequencedMessage where
  | orderAcceptedMessage (message : OrderAcceptedMessage) -- 'A' 0x41
  | orderRejectedMessage (message : OrderRejectedMessage) -- 'J' 0x4A
  | orderReplacedMessage (message : OrderReplacedMessage) -- 'U' 0x55
  | orderCancelledMessage (message : OrderCancelledMessage) -- 'C' 0x43
  | orderExecutedMessage (message : OrderExecutedMessage) -- 'E' 0x45
  deriving DecidableEq, Repr

namespace SequencedMessage

/-- The Sequenced Message Type each message is sent under -/
def tag : SequencedMessage → BitVec 8
  | .orderAcceptedMessage _ => 65
  | .orderRejectedMessage _ => 74
  | .orderReplacedMessage _ => 85
  | .orderCancelledMessage _ => 67
  | .orderExecutedMessage _ => 69

def encode : SequencedMessage → List UInt8
  | .orderAcceptedMessage message => OrderAcceptedMessage.encode message
  | .orderRejectedMessage message => OrderRejectedMessage.encode message
  | .orderReplacedMessage message => OrderReplacedMessage.encode message
  | .orderCancelledMessage message => OrderCancelledMessage.encode message
  | .orderExecutedMessage message => OrderExecutedMessage.encode message

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (SequencedMessage × List UInt8) :=
  if tag = 65 then (OrderAcceptedMessage.decode bytes).map fun (message, rest) => (.orderAcceptedMessage message, rest)
  else if tag = 74 then (OrderRejectedMessage.decode bytes).map fun (message, rest) => (.orderRejectedMessage message, rest)
  else if tag = 85 then (OrderReplacedMessage.decode bytes).map fun (message, rest) => (.orderReplacedMessage message, rest)
  else if tag = 67 then (OrderCancelledMessage.decode bytes).map fun (message, rest) => (.orderCancelledMessage message, rest)
  else if tag = 69 then (OrderExecutedMessage.decode bytes).map fun (message, rest) => (.orderExecutedMessage message, rest)
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
theorem encode_length_le (message : SequencedDataPacket) : (encode message).length ≤ 188 := by
  unfold encode
  cases message.sequencedMessage with
  | orderAcceptedMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderAcceptedMessage.encode_length]
    omega
  | orderRejectedMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderRejectedMessage.encode_length]
    omega
  | orderReplacedMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderReplacedMessage.encode_length]
    omega
  | orderCancelledMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderCancelledMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderExecutedMessage.encode_length]
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
  | debugPacket (message : DebugPacket) -- '+' 0x2B
  | loginAcceptedPacket (message : LoginAcceptedPacket) -- 'A' 0x41
  | loginRejectedPacket (message : LoginRejectedPacket) -- 'J' 0x4A
  | sequencedDataPacket (message : SequencedDataPacket) -- 'S' 0x53
  | serverHeartbeat (message : ServerHeartbeat) -- 'H' 0x48
  | endOfSession (message : EndOfSession) -- 'Z' 0x5A
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

end Omi.AsxAsxsecuritiesTradeOuchV36Server
