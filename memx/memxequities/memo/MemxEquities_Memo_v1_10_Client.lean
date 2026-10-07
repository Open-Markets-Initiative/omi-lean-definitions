import Wire

/-!
# The Members Exchange Members Orders v1.10

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Exec Inst is a bit field set, proven as its 2 byte integer rather than bit by bit.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.MemxMemxequitiesMemoSbeV110Client

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

/-- New Order Single Message: 96 bytes -/
structure NewOrderSingleMessage where
  clordid : Alpha 16
  mpidOptional : Alpha 4
  symbol : Alpha 6
  symbolSfx : Alpha 6
  side : Side
  orderQty : BitVec 32
  ordType : OrdType
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
  linkIdOptional : Alpha 4
  deriving DecidableEq, Repr

namespace NewOrderSingleMessage

def encode (message : NewOrderSingleMessage) : List UInt8 :=
  Alpha.encode message.clordid
    ++ (Alpha.encode message.mpidOptional
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.symbolSfx
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.orderQty
    ++ (OrdType.encode message.ordType
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
    ++ (Alpha.encode message.linkIdOptional)))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (NewOrderSingleMessage × List UInt8) := do
  let (clordid, bytes) ← Alpha.decode 16 bytes
  let (mpidOptional, bytes) ← Alpha.decode 4 bytes
  let (symbol, bytes) ← Alpha.decode 6 bytes
  let (symbolSfx, bytes) ← Alpha.decode 6 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderQty, bytes) ← decodeUInt 4 bytes
  let (ordType, bytes) ← OrdType.decode bytes
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
  let (linkIdOptional, bytes) ← Alpha.decode 4 bytes
  pure ({ clordid, mpidOptional, symbol, symbolSfx, side, orderQty, ordType, price, timeInForce, orderCapacity, custOrderCapacity, execInst, pegOffsetValue, pegPriceType, expireTime, minQty, displayQty, displayMethod, reserveReplenishTiming, displayMinIncr, locateReqd, repriceFrequency, repriceBehavior, cancelGroupId, stpGroupId, selfTradePrevention, riskGroupId, linkIdOptional }, bytes)

@[simp] theorem encode_length (message : NewOrderSingleMessage) : (encode message).length = 96 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, Side.encode_length, encodeUInt_length, OrdType.encode_length, TimeInForce.encode_length, OrderCapacity.encode_length, DisplayMethod.encode_length]

theorem encode_length_pos (message : NewOrderSingleMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

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
  rw [Alpha.decode_encode, some_bind]
  rfl

end NewOrderSingleMessage

/-- Order Cancel Replace Request Message: 67 bytes -/
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
    ++ (Alpha.encode message.linkIdOptional))))))))))

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
  pure ({ origclordid, clordid, symbol, symbolSfx, side, orderQty, ordType, price, displayQty, locateReqd, linkIdOptional }, bytes)

@[simp] theorem encode_length (message : OrderCancelReplaceRequestMessage) : (encode message).length = 67 := by
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

/-- Any Client Payload, selected by Template Id -/
inductive ClientPayload where
  | newOrderSingleMessage (message : NewOrderSingleMessage) -- 1
  | orderCancelReplaceRequestMessage (message : OrderCancelReplaceRequestMessage) -- 2
  | orderCancelRequestMessage (message : OrderCancelRequestMessage) -- 3
  | massCancelRequestMessage (message : MassCancelRequestMessage) -- 4
  deriving DecidableEq, Repr

namespace ClientPayload

/-- The Template Id each message is sent under -/
def tag : ClientPayload → BitVec 8
  | .newOrderSingleMessage _ => 1
  | .orderCancelReplaceRequestMessage _ => 2
  | .orderCancelRequestMessage _ => 3
  | .massCancelRequestMessage _ => 4

def encode : ClientPayload → List UInt8
  | .newOrderSingleMessage message => NewOrderSingleMessage.encode message
  | .orderCancelReplaceRequestMessage message => OrderCancelReplaceRequestMessage.encode message
  | .orderCancelRequestMessage message => OrderCancelRequestMessage.encode message
  | .massCancelRequestMessage message => MassCancelRequestMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ClientPayload) : (encode message).length ≤ 96 := by
  cases message with
  | newOrderSingleMessage inner =>
    simp only [encode, NewOrderSingleMessage.encode_length]
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

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ClientPayload × List UInt8) :=
  if tag = 1 then (NewOrderSingleMessage.decode bytes).map fun (message, rest) => (.newOrderSingleMessage message, rest)
  else if tag = 2 then (OrderCancelReplaceRequestMessage.decode bytes).map fun (message, rest) => (.orderCancelReplaceRequestMessage message, rest)
  else if tag = 3 then (OrderCancelRequestMessage.decode bytes).map fun (message, rest) => (.orderCancelRequestMessage message, rest)
  else if tag = 4 then (MassCancelRequestMessage.decode bytes).map fun (message, rest) => (.massCancelRequestMessage message, rest)
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
theorem encode_length_le (message : ClientSbeMessage) : (encode message).length ≤ 102 := by
  unfold encode
  cases message.clientPayload with
  | newOrderSingleMessage inner =>
    simp only [ClientPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, NewOrderSingleMessage.encode_length]
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

end Omi.MemxMemxequitiesMemoSbeV110Client
