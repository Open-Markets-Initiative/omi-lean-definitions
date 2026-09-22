import Omi.Wire

/-!
# Australian Securities Exchange Asx Trade v2.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Unsequenced Data Packet is not framed: its length Packet Length is not an integer it reads.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.AsxAsxsecuritiesTradeOuchV20Client

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x42, 0x53, 0x54, 0x43]

inductive Side where
  | buyOrder -- Buy Order
  | sellOrder -- Sell Order
  | shortSellOrder -- Short Sell Order
  | buyOrderInACombination -- Buy Order In A Combination
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buyOrder => 0x42
  | .sellOrder => 0x53
  | .shortSellOrder => 0x54
  | .buyOrderInACombination => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x42 then .buyOrder
  else if byte = 0x53 then .sellOrder
  else if byte = 0x54 then .shortSellOrder
  else .buyOrderInACombination

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buyOrder => decide
  | sellOrder => decide
  | shortSellOrder => decide
  | buyOrderInACombination => decide
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
  | mixedAgencyAndPrincipal -- Mixed Agency And Principal
  | unlisted (byte : { byte : UInt8 // byte ∉ CapacityOfParticipant.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CapacityOfParticipant

def toByte : CapacityOfParticipant → UInt8
  | .agency => 0x41
  | .principal => 0x50
  | .mixedAgencyAndPrincipal => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CapacityOfParticipant :=
  if byte = 0x41 then .agency
  else if byte = 0x50 then .principal
  else .mixedAgencyAndPrincipal

def ofByte (byte : UInt8) : CapacityOfParticipant :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CapacityOfParticipant) : ofByte value.toByte = value := by
  cases value with
  | agency => decide
  | principal => decide
  | mixedAgencyAndPrincipal => decide
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
  | falseDefault -- False Default
  | unlisted (byte : { byte : UInt8 // byte ∉ DirectedWholesale.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace DirectedWholesale

def toByte : DirectedWholesale → UInt8
  | .true_ => 0x59
  | .falseDefault => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : DirectedWholesale :=
  if byte = 0x59 then .true_
  else .falseDefault

def ofByte (byte : UInt8) : DirectedWholesale :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : DirectedWholesale) : ofByte value.toByte = value := by
  cases value with
  | true_ => decide
  | falseDefault => decide
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

/-- Enter Order Message: 156 bytes -/
structure EnterOrderMessage where
  orderToken : Alpha 14
  orderBookId : BitVec 32
  side : Side
  quantity : BitVec 64
  price : BitVec 32
  timeInForce : BitVec 8
  openClose : BitVec 8
  clientAccount : Alpha 10
  customerInfo : Alpha 15
  exchangeInfo : Alpha 32
  clearingParticipant : Alpha 1
  crossingKey : BitVec 32
  capacityOfParticipant : CapacityOfParticipant
  directedWholesale : DirectedWholesale
  executionVenue : Alpha 4
  intermediaryId : Alpha 10
  orderOrigin : Alpha 20
  filler : Alpha 8
  ouchOrderType : OuchOrderType
  shortSellQuantity : BitVec 64
  minimumAcceptableQuantity : BitVec 64
  deriving DecidableEq, Repr

namespace EnterOrderMessage

def encode (message : EnterOrderMessage) : List UInt8 :=
  Alpha.encode message.orderToken
    ++ (encodeUInt 4 message.orderBookId
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.quantity
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 1 message.timeInForce
    ++ (encodeUInt 1 message.openClose
    ++ (Alpha.encode message.clientAccount
    ++ (Alpha.encode message.customerInfo
    ++ (Alpha.encode message.exchangeInfo
    ++ (Alpha.encode message.clearingParticipant
    ++ (encodeUInt 4 message.crossingKey
    ++ (CapacityOfParticipant.encode message.capacityOfParticipant
    ++ (DirectedWholesale.encode message.directedWholesale
    ++ (Alpha.encode message.executionVenue
    ++ (Alpha.encode message.intermediaryId
    ++ (Alpha.encode message.orderOrigin
    ++ (Alpha.encode message.filler
    ++ (OuchOrderType.encode message.ouchOrderType
    ++ (encodeUInt 8 message.shortSellQuantity
    ++ (encodeUInt 8 message.minimumAcceptableQuantity))))))))))))))))))))

def decode (bytes : List UInt8) : Option (EnterOrderMessage × List UInt8) := do
  let (orderToken, bytes) ← Alpha.decode 14 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (quantity, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (openClose, bytes) ← decodeUInt 1 bytes
  let (clientAccount, bytes) ← Alpha.decode 10 bytes
  let (customerInfo, bytes) ← Alpha.decode 15 bytes
  let (exchangeInfo, bytes) ← Alpha.decode 32 bytes
  let (clearingParticipant, bytes) ← Alpha.decode 1 bytes
  let (crossingKey, bytes) ← decodeUInt 4 bytes
  let (capacityOfParticipant, bytes) ← CapacityOfParticipant.decode bytes
  let (directedWholesale, bytes) ← DirectedWholesale.decode bytes
  let (executionVenue, bytes) ← Alpha.decode 4 bytes
  let (intermediaryId, bytes) ← Alpha.decode 10 bytes
  let (orderOrigin, bytes) ← Alpha.decode 20 bytes
  let (filler, bytes) ← Alpha.decode 8 bytes
  let (ouchOrderType, bytes) ← OuchOrderType.decode bytes
  let (shortSellQuantity, bytes) ← decodeUInt 8 bytes
  let (minimumAcceptableQuantity, bytes) ← decodeUInt 8 bytes
  pure ({ orderToken, orderBookId, side, quantity, price, timeInForce, openClose, clientAccount, customerInfo, exchangeInfo, clearingParticipant, crossingKey, capacityOfParticipant, directedWholesale, executionVenue, intermediaryId, orderOrigin, filler, ouchOrderType, shortSellQuantity, minimumAcceptableQuantity }, bytes)

@[simp] theorem encode_length (message : EnterOrderMessage) : (encode message).length = 156 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, Side.encode_length, CapacityOfParticipant.encode_length, DirectedWholesale.encode_length, OuchOrderType.encode_length]

theorem encode_length_pos (message : EnterOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EnterOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OuchOrderType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end EnterOrderMessage

/-- Replace Order Message: 158 bytes -/
structure ReplaceOrderMessage where
  existingOrderToken : Alpha 14
  replacementOrderToken : Alpha 14
  quantity : BitVec 64
  price : BitVec 32
  openClose : BitVec 8
  clientAccount : Alpha 10
  customerInfo : Alpha 15
  exchangeInfo : Alpha 32
  capacityOfParticipant : CapacityOfParticipant
  directedWholesale : DirectedWholesale
  executionVenue : Alpha 4
  intermediaryId : Alpha 10
  orderOrigin : Alpha 20
  filler : Alpha 8
  shortSellQuantity : BitVec 64
  minimumAcceptableQuantity : BitVec 64
  deriving DecidableEq, Repr

namespace ReplaceOrderMessage

def encode (message : ReplaceOrderMessage) : List UInt8 :=
  Alpha.encode message.existingOrderToken
    ++ (Alpha.encode message.replacementOrderToken
    ++ (encodeUInt 8 message.quantity
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 1 message.openClose
    ++ (Alpha.encode message.clientAccount
    ++ (Alpha.encode message.customerInfo
    ++ (Alpha.encode message.exchangeInfo
    ++ (CapacityOfParticipant.encode message.capacityOfParticipant
    ++ (DirectedWholesale.encode message.directedWholesale
    ++ (Alpha.encode message.executionVenue
    ++ (Alpha.encode message.intermediaryId
    ++ (Alpha.encode message.orderOrigin
    ++ (Alpha.encode message.filler
    ++ (encodeUInt 8 message.shortSellQuantity
    ++ (encodeUInt 8 message.minimumAcceptableQuantity)))))))))))))))

def decode (bytes : List UInt8) : Option (ReplaceOrderMessage × List UInt8) := do
  let (existingOrderToken, bytes) ← Alpha.decode 14 bytes
  let (replacementOrderToken, bytes) ← Alpha.decode 14 bytes
  let (quantity, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (openClose, bytes) ← decodeUInt 1 bytes
  let (clientAccount, bytes) ← Alpha.decode 10 bytes
  let (customerInfo, bytes) ← Alpha.decode 15 bytes
  let (exchangeInfo, bytes) ← Alpha.decode 32 bytes
  let (capacityOfParticipant, bytes) ← CapacityOfParticipant.decode bytes
  let (directedWholesale, bytes) ← DirectedWholesale.decode bytes
  let (executionVenue, bytes) ← Alpha.decode 4 bytes
  let (intermediaryId, bytes) ← Alpha.decode 10 bytes
  let (orderOrigin, bytes) ← Alpha.decode 20 bytes
  let (filler, bytes) ← Alpha.decode 8 bytes
  let (shortSellQuantity, bytes) ← decodeUInt 8 bytes
  let (minimumAcceptableQuantity, bytes) ← decodeUInt 8 bytes
  pure ({ existingOrderToken, replacementOrderToken, quantity, price, openClose, clientAccount, customerInfo, exchangeInfo, capacityOfParticipant, directedWholesale, executionVenue, intermediaryId, orderOrigin, filler, shortSellQuantity, minimumAcceptableQuantity }, bytes)

@[simp] theorem encode_length (message : ReplaceOrderMessage) : (encode message).length = 158 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, CapacityOfParticipant.encode_length, DirectedWholesale.encode_length]

theorem encode_length_pos (message : ReplaceOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReplaceOrderMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ReplaceOrderMessage

/-- Cancel Order Message: 14 bytes -/
structure CancelOrderMessage where
  orderToken : Alpha 14
  deriving DecidableEq, Repr

namespace CancelOrderMessage

def encode (message : CancelOrderMessage) : List UInt8 :=
  Alpha.encode message.orderToken

def decode (bytes : List UInt8) : Option (CancelOrderMessage × List UInt8) := do
  let (orderToken, bytes) ← Alpha.decode 14 bytes
  pure ({ orderToken }, bytes)

@[simp] theorem encode_length (message : CancelOrderMessage) : (encode message).length = 14 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : CancelOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancelOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end CancelOrderMessage

/-- Cancel By Order Id Message: 13 bytes -/
structure CancelByOrderIdMessage where
  orderBookId : BitVec 32
  side : Side
  orderId : BitVec 64
  deriving DecidableEq, Repr

namespace CancelByOrderIdMessage

def encode (message : CancelByOrderIdMessage) : List UInt8 :=
  encodeUInt 4 message.orderBookId
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.orderId))

def decode (bytes : List UInt8) : Option (CancelByOrderIdMessage × List UInt8) := do
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  pure ({ orderBookId, side, orderId }, bytes)

@[simp] theorem encode_length (message : CancelByOrderIdMessage) : (encode message).length = 13 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length]

theorem encode_length_pos (message : CancelByOrderIdMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancelByOrderIdMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CancelByOrderIdMessage

/-- Any Unsequenced Message, selected by Unsequenced Message Type -/
inductive UnsequencedMessage where
  | enterOrderMessage (message : EnterOrderMessage) -- "O" 0x4F
  | replaceOrderMessage (message : ReplaceOrderMessage) -- "U" 0x55
  | cancelOrderMessage (message : CancelOrderMessage) -- "X" 0x58
  | cancelByOrderIdMessage (message : CancelByOrderIdMessage) -- "Y" 0x59
  deriving DecidableEq, Repr

namespace UnsequencedMessage

/-- The Unsequenced Message Type each message is sent under -/
def tag : UnsequencedMessage → BitVec 8
  | .enterOrderMessage _ => 79
  | .replaceOrderMessage _ => 85
  | .cancelOrderMessage _ => 88
  | .cancelByOrderIdMessage _ => 89

def encode : UnsequencedMessage → List UInt8
  | .enterOrderMessage message => EnterOrderMessage.encode message
  | .replaceOrderMessage message => ReplaceOrderMessage.encode message
  | .cancelOrderMessage message => CancelOrderMessage.encode message
  | .cancelByOrderIdMessage message => CancelByOrderIdMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : UnsequencedMessage) : (encode message).length ≤ 158 := by
  cases message with
  | enterOrderMessage inner =>
    simp only [encode, EnterOrderMessage.encode_length]
    omega
  | replaceOrderMessage inner =>
    simp only [encode, ReplaceOrderMessage.encode_length]
    omega
  | cancelOrderMessage inner =>
    simp only [encode, CancelOrderMessage.encode_length]
    omega
  | cancelByOrderIdMessage inner =>
    simp only [encode, CancelByOrderIdMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (UnsequencedMessage × List UInt8) :=
  if tag = 79 then (EnterOrderMessage.decode bytes).map fun (message, rest) => (.enterOrderMessage message, rest)
  else if tag = 85 then (ReplaceOrderMessage.decode bytes).map fun (message, rest) => (.replaceOrderMessage message, rest)
  else if tag = 88 then (CancelOrderMessage.decode bytes).map fun (message, rest) => (.cancelOrderMessage message, rest)
  else if tag = 89 then (CancelByOrderIdMessage.decode bytes).map fun (message, rest) => (.cancelByOrderIdMessage message, rest)
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
theorem encode_length_le (message : UnsequencedDataPacket) : (encode message).length ≤ 159 := by
  unfold encode
  cases message.unsequencedMessage with
  | enterOrderMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, EnterOrderMessage.encode_length]
    omega
  | replaceOrderMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, ReplaceOrderMessage.encode_length]
    omega
  | cancelOrderMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, CancelOrderMessage.encode_length]
    omega
  | cancelByOrderIdMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, CancelByOrderIdMessage.encode_length]
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
theorem encode_length_le (message : ClientPayload) : (encode message).length ≤ 159 := by
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

end Omi.AsxAsxsecuritiesTradeOuchV20Client
