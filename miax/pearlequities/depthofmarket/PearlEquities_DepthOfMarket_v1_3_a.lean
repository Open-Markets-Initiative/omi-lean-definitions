import Omi.Wire

/-!
# Miami International Holdings Depth Of Market v1.3.a

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Modify Order Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Order Execution Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Trade Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Application Message is not framed: its length Mach Packet Length is not an integer it reads.

Note: Packet is not framed: its length Mach Packet Length is not an integer it reads.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.MiaxPearlequitiesDepthofmarketMachV13A

/-- Test Security Indicator: one byte code -/
def TestSecurityIndicator.codes : List UInt8 :=
  [0x59, 0x4E]

inductive TestSecurityIndicator where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ TestSecurityIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TestSecurityIndicator

def toByte : TestSecurityIndicator → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TestSecurityIndicator :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : TestSecurityIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TestSecurityIndicator) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TestSecurityIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TestSecurityIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TestSecurityIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TestSecurityIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TestSecurityIndicator

/-- Primary Market Code: one byte code -/
def PrimaryMarketCode.codes : List UInt8 :=
  [0x41, 0x42, 0x43, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x50, 0x51, 0x55, 0x56, 0x57, 0x58, 0x59, 0x5A]

inductive PrimaryMarketCode where
  | nyseAmerican -- Nyse American
  | nasdaqBx -- Nasdaq Bx
  | nyseNational -- Nyse National
  | miaxPearlEquities -- Miax Pearl Equities
  | nasdaqIse -- Nasdaq Ise
  | cboeEdgaExchange -- Cboe Edga Exchange
  | cboeEdgxExchange -- Cboe Edgx Exchange
  | longTermStockExchange -- Long Term Stock Exchange
  | nyseChicago -- Nyse Chicago
  | newYorkStockExchange -- New York Stock Exchange
  | nyseArca -- Nyse Arca
  | nasdaq -- Nasdaq
  | membersExchange -- Members Exchange
  | investorsExchange -- Investors Exchange
  | cboeStockExchange -- Cboe Stock Exchange
  | nasdaqPhlx -- Nasdaq Phlx
  | cboeByxExchange -- Cboe Byx Exchange
  | cboeBzxExchange -- Cboe Bzx Exchange
  | unlisted (byte : { byte : UInt8 // byte ∉ PrimaryMarketCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PrimaryMarketCode

def toByte : PrimaryMarketCode → UInt8
  | .nyseAmerican => 0x41
  | .nasdaqBx => 0x42
  | .nyseNational => 0x43
  | .miaxPearlEquities => 0x48
  | .nasdaqIse => 0x49
  | .cboeEdgaExchange => 0x4A
  | .cboeEdgxExchange => 0x4B
  | .longTermStockExchange => 0x4C
  | .nyseChicago => 0x4D
  | .newYorkStockExchange => 0x4E
  | .nyseArca => 0x50
  | .nasdaq => 0x51
  | .membersExchange => 0x55
  | .investorsExchange => 0x56
  | .cboeStockExchange => 0x57
  | .nasdaqPhlx => 0x58
  | .cboeByxExchange => 0x59
  | .cboeBzxExchange => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PrimaryMarketCode :=
  if byte = 0x41 then .nyseAmerican
  else if byte = 0x42 then .nasdaqBx
  else if byte = 0x43 then .nyseNational
  else if byte = 0x48 then .miaxPearlEquities
  else if byte = 0x49 then .nasdaqIse
  else if byte = 0x4A then .cboeEdgaExchange
  else if byte = 0x4B then .cboeEdgxExchange
  else if byte = 0x4C then .longTermStockExchange
  else if byte = 0x4D then .nyseChicago
  else if byte = 0x4E then .newYorkStockExchange
  else if byte = 0x50 then .nyseArca
  else if byte = 0x51 then .nasdaq
  else if byte = 0x55 then .membersExchange
  else if byte = 0x56 then .investorsExchange
  else if byte = 0x57 then .cboeStockExchange
  else if byte = 0x58 then .nasdaqPhlx
  else if byte = 0x59 then .cboeByxExchange
  else .cboeBzxExchange

def ofByte (byte : UInt8) : PrimaryMarketCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PrimaryMarketCode) : ofByte value.toByte = value := by
  cases value with
  | nyseAmerican => decide
  | nasdaqBx => decide
  | nyseNational => decide
  | miaxPearlEquities => decide
  | nasdaqIse => decide
  | cboeEdgaExchange => decide
  | cboeEdgxExchange => decide
  | longTermStockExchange => decide
  | nyseChicago => decide
  | newYorkStockExchange => decide
  | nyseArca => decide
  | nasdaq => decide
  | membersExchange => decide
  | investorsExchange => decide
  | cboeStockExchange => decide
  | nasdaqPhlx => decide
  | cboeByxExchange => decide
  | cboeBzxExchange => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PrimaryMarketCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PrimaryMarketCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PrimaryMarketCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PrimaryMarketCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PrimaryMarketCode

/-- System Status: one byte code -/
def SystemStatus.codes : List UInt8 :=
  [0x53, 0x43, 0x31, 0x32]

inductive SystemStatus where
  | startOfSystemHours -- Start Of System Hours
  | endOfSystemHours -- End Of System Hours
  | startOfTestSession -- Start Of Test Session
  | endOfTestSession -- End Of Test Session
  | unlisted (byte : { byte : UInt8 // byte ∉ SystemStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SystemStatus

def toByte : SystemStatus → UInt8
  | .startOfSystemHours => 0x53
  | .endOfSystemHours => 0x43
  | .startOfTestSession => 0x31
  | .endOfTestSession => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SystemStatus :=
  if byte = 0x53 then .startOfSystemHours
  else if byte = 0x43 then .endOfSystemHours
  else if byte = 0x31 then .startOfTestSession
  else .endOfTestSession

def ofByte (byte : UInt8) : SystemStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SystemStatus) : ofByte value.toByte = value := by
  cases value with
  | startOfSystemHours => decide
  | endOfSystemHours => decide
  | startOfTestSession => decide
  | endOfTestSession => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SystemStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SystemStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SystemStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SystemStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SystemStatus

/-- Short Sale Restriction: one byte code -/
def ShortSaleRestriction.codes : List UInt8 :=
  [0x59, 0x4E]

inductive ShortSaleRestriction where
  | ssrInEffect -- Ssr In Effect
  | ssrNotInEffect -- Ssr Not In Effect
  | unlisted (byte : { byte : UInt8 // byte ∉ ShortSaleRestriction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ShortSaleRestriction

def toByte : ShortSaleRestriction → UInt8
  | .ssrInEffect => 0x59
  | .ssrNotInEffect => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ShortSaleRestriction :=
  if byte = 0x59 then .ssrInEffect
  else .ssrNotInEffect

def ofByte (byte : UInt8) : ShortSaleRestriction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ShortSaleRestriction) : ofByte value.toByte = value := by
  cases value with
  | ssrInEffect => decide
  | ssrNotInEffect => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ShortSaleRestriction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ShortSaleRestriction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ShortSaleRestriction) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ShortSaleRestriction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ShortSaleRestriction

/-- Order Side: one byte code -/
def OrderSide.codes : List UInt8 :=
  [0x42, 0x53]

inductive OrderSide where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderSide

def toByte : OrderSide → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderSide :=
  if byte = 0x42 then .buy
  else .sell

def ofByte (byte : UInt8) : OrderSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderSide) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderSide) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OrderSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderSide

/-- Heartbeat: 0 bytes -/
structure Heartbeat where
  deriving DecidableEq, Repr

namespace Heartbeat

def encode (_ : Heartbeat) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (Heartbeat × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : Heartbeat) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : Heartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end Heartbeat

/-- Start Of Session: 0 bytes -/
structure StartOfSession where
  deriving DecidableEq, Repr

namespace StartOfSession

def encode (_ : StartOfSession) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (StartOfSession × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : StartOfSession) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : StartOfSession) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end StartOfSession

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

/-- System Time Message: 4 bytes -/
structure SystemTimeMessage where
  seconds : BitVec 32
  deriving DecidableEq, Repr

namespace SystemTimeMessage

def encode (message : SystemTimeMessage) : List UInt8 :=
  encodeUIntLE 4 message.seconds

def decode (bytes : List UInt8) : Option (SystemTimeMessage × List UInt8) := do
  let (seconds, bytes) ← decodeUIntLE 4 bytes
  pure ({ seconds }, bytes)

@[simp] theorem encode_length (message : SystemTimeMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : SystemTimeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemTimeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SystemTimeMessage

/-- Symbol Update Message: 41 bytes -/
structure SymbolUpdateMessage where
  nanoseconds : BitVec 32
  symbolId : BitVec 32
  tickerSymbol : Alpha 11
  reserved1 : Alpha 1
  testSecurityIndicator : TestSecurityIndicator
  spare : BitVec 8
  lotSize : BitVec 16
  openingTime : Alpha 8
  closingTime : Alpha 8
  primaryMarketCode : PrimaryMarketCode
  deriving DecidableEq, Repr

namespace SymbolUpdateMessage

def encode (message : SymbolUpdateMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.symbolId
    ++ (Alpha.encode message.tickerSymbol
    ++ (Alpha.encode message.reserved1
    ++ (TestSecurityIndicator.encode message.testSecurityIndicator
    ++ (encodeUIntLE 1 message.spare
    ++ (encodeUIntLE 2 message.lotSize
    ++ (Alpha.encode message.openingTime
    ++ (Alpha.encode message.closingTime
    ++ (PrimaryMarketCode.encode message.primaryMarketCode)))))))))

def decode (bytes : List UInt8) : Option (SymbolUpdateMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (tickerSymbol, bytes) ← Alpha.decode 11 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (testSecurityIndicator, bytes) ← TestSecurityIndicator.decode bytes
  let (spare, bytes) ← decodeUIntLE 1 bytes
  let (lotSize, bytes) ← decodeUIntLE 2 bytes
  let (openingTime, bytes) ← Alpha.decode 8 bytes
  let (closingTime, bytes) ← Alpha.decode 8 bytes
  let (primaryMarketCode, bytes) ← PrimaryMarketCode.decode bytes
  pure ({ nanoseconds, symbolId, tickerSymbol, reserved1, testSecurityIndicator, spare, lotSize, openingTime, closingTime, primaryMarketCode }, bytes)

@[simp] theorem encode_length (message : SymbolUpdateMessage) : (encode message).length = 41 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TestSecurityIndicator.encode_length, PrimaryMarketCode.encode_length]

theorem encode_length_pos (message : SymbolUpdateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SymbolUpdateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TestSecurityIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [PrimaryMarketCode.decode_encode, some_bind]
  rfl

end SymbolUpdateMessage

/-- System State Message: 14 bytes -/
structure SystemStateMessage where
  nanoseconds : BitVec 32
  doMVersion : Alpha 8
  sessionId : BitVec 8
  systemStatus : SystemStatus
  deriving DecidableEq, Repr

namespace SystemStateMessage

def encode (message : SystemStateMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (Alpha.encode message.doMVersion
    ++ (encodeUIntLE 1 message.sessionId
    ++ (SystemStatus.encode message.systemStatus)))

def decode (bytes : List UInt8) : Option (SystemStateMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (doMVersion, bytes) ← Alpha.decode 8 bytes
  let (sessionId, bytes) ← decodeUIntLE 1 bytes
  let (systemStatus, bytes) ← SystemStatus.decode bytes
  pure ({ nanoseconds, doMVersion, sessionId, systemStatus }, bytes)

@[simp] theorem encode_length (message : SystemStateMessage) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, SystemStatus.encode_length]

theorem encode_length_pos (message : SystemStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [SystemStatus.decode_encode, some_bind]
  rfl

end SystemStateMessage

/-- Security Trading Status Notification Message: 11 bytes -/
structure SecurityTradingStatusNotificationMessage where
  nanoseconds : BitVec 32
  symbolId : BitVec 32
  tradingStatus : BitVec 8
  marketState : BitVec 8
  shortSaleRestriction : ShortSaleRestriction
  deriving DecidableEq, Repr

namespace SecurityTradingStatusNotificationMessage

def encode (message : SecurityTradingStatusNotificationMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.symbolId
    ++ (encodeUIntLE 1 message.tradingStatus
    ++ (encodeUIntLE 1 message.marketState
    ++ (ShortSaleRestriction.encode message.shortSaleRestriction))))

def decode (bytes : List UInt8) : Option (SecurityTradingStatusNotificationMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (tradingStatus, bytes) ← decodeUIntLE 1 bytes
  let (marketState, bytes) ← decodeUIntLE 1 bytes
  let (shortSaleRestriction, bytes) ← ShortSaleRestriction.decode bytes
  pure ({ nanoseconds, symbolId, tradingStatus, marketState, shortSaleRestriction }, bytes)

@[simp] theorem encode_length (message : SecurityTradingStatusNotificationMessage) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, ShortSaleRestriction.encode_length]

theorem encode_length_pos (message : SecurityTradingStatusNotificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityTradingStatusNotificationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [ShortSaleRestriction.decode_encode, some_bind]
  rfl

end SecurityTradingStatusNotificationMessage

/-- Symbol Clear Message: 8 bytes -/
structure SymbolClearMessage where
  nanoseconds : BitVec 32
  symbolId : BitVec 32
  deriving DecidableEq, Repr

namespace SymbolClearMessage

def encode (message : SymbolClearMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.symbolId)

def decode (bytes : List UInt8) : Option (SymbolClearMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  pure ({ nanoseconds, symbolId }, bytes)

@[simp] theorem encode_length (message : SymbolClearMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : SymbolClearMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SymbolClearMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SymbolClearMessage

/-- Add Order Message: 33 bytes -/
structure AddOrderMessage where
  nanoseconds : BitVec 32
  symbolId : BitVec 32
  orderId : BitVec 64
  orderSide : OrderSide
  price : BitVec 64
  size : BitVec 32
  attributableId : Alpha 4
  deriving DecidableEq, Repr

namespace AddOrderMessage

def encode (message : AddOrderMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.symbolId
    ++ (encodeUIntLE 8 message.orderId
    ++ (OrderSide.encode message.orderSide
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.size
    ++ (Alpha.encode message.attributableId))))))

def decode (bytes : List UInt8) : Option (AddOrderMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (orderSide, bytes) ← OrderSide.decode bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (size, bytes) ← decodeUIntLE 4 bytes
  let (attributableId, bytes) ← Alpha.decode 4 bytes
  pure ({ nanoseconds, symbolId, orderId, orderSide, price, size, attributableId }, bytes)

@[simp] theorem encode_length (message : AddOrderMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, OrderSide.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : AddOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrderSide.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end AddOrderMessage

/-- Modify Order Message: 29 bytes -/
structure ModifyOrderMessage where
  nanoseconds : BitVec 32
  symbolId : BitVec 32
  orderId : BitVec 64
  price : BitVec 64
  size : BitVec 32
  modifyOrderFlags : BitVec 8
  deriving DecidableEq, Repr

namespace ModifyOrderMessage

def encode (message : ModifyOrderMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.symbolId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.size
    ++ (encodeUIntLE 1 message.modifyOrderFlags)))))

def decode (bytes : List UInt8) : Option (ModifyOrderMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (size, bytes) ← decodeUIntLE 4 bytes
  let (modifyOrderFlags, bytes) ← decodeUIntLE 1 bytes
  pure ({ nanoseconds, symbolId, orderId, price, size, modifyOrderFlags }, bytes)

@[simp] theorem encode_length (message : ModifyOrderMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : ModifyOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ModifyOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ModifyOrderMessage

/-- Delete Order Message: 16 bytes -/
structure DeleteOrderMessage where
  nanoseconds : BitVec 32
  symbolId : BitVec 32
  orderId : BitVec 64
  deriving DecidableEq, Repr

namespace DeleteOrderMessage

def encode (message : DeleteOrderMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.symbolId
    ++ (encodeUIntLE 8 message.orderId))

def decode (bytes : List UInt8) : Option (DeleteOrderMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  pure ({ nanoseconds, symbolId, orderId }, bytes)

@[simp] theorem encode_length (message : DeleteOrderMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : DeleteOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DeleteOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end DeleteOrderMessage

/-- Order Execution Message: 37 bytes -/
structure OrderExecutionMessage where
  nanoseconds : BitVec 32
  symbolId : BitVec 32
  orderId : BitVec 64
  tradeId : BitVec 64
  price : BitVec 64
  size : BitVec 32
  orderExecutionFlags : BitVec 8
  deriving DecidableEq, Repr

namespace OrderExecutionMessage

def encode (message : OrderExecutionMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.symbolId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.tradeId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.size
    ++ (encodeUIntLE 1 message.orderExecutionFlags))))))

def decode (bytes : List UInt8) : Option (OrderExecutionMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (tradeId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (size, bytes) ← decodeUIntLE 4 bytes
  let (orderExecutionFlags, bytes) ← decodeUIntLE 1 bytes
  pure ({ nanoseconds, symbolId, orderId, tradeId, price, size, orderExecutionFlags }, bytes)

@[simp] theorem encode_length (message : OrderExecutionMessage) : (encode message).length = 37 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderExecutionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecutionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderExecutionMessage

/-- Trade Message: 30 bytes -/
structure TradeMessage where
  nanoseconds : BitVec 32
  symbolId : BitVec 32
  tradeId : BitVec 64
  correctionNumber : BitVec 8
  price : BitVec 64
  size : BitVec 32
  tradeFlags : BitVec 8
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.symbolId
    ++ (encodeUIntLE 8 message.tradeId
    ++ (encodeUIntLE 1 message.correctionNumber
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.size
    ++ (encodeUIntLE 1 message.tradeFlags))))))

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 8 bytes
  let (correctionNumber, bytes) ← decodeUIntLE 1 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (size, bytes) ← decodeUIntLE 4 bytes
  let (tradeFlags, bytes) ← decodeUIntLE 1 bytes
  pure ({ nanoseconds, symbolId, tradeId, correctionNumber, price, size, tradeFlags }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : TradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeMessage

/-- Trade Cancel Message: 29 bytes -/
structure TradeCancelMessage where
  nanoseconds : BitVec 32
  symbolId : BitVec 32
  tradeId : BitVec 64
  correctionNumber : BitVec 8
  price : BitVec 64
  size : BitVec 32
  deriving DecidableEq, Repr

namespace TradeCancelMessage

def encode (message : TradeCancelMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.symbolId
    ++ (encodeUIntLE 8 message.tradeId
    ++ (encodeUIntLE 1 message.correctionNumber
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.size)))))

def decode (bytes : List UInt8) : Option (TradeCancelMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 8 bytes
  let (correctionNumber, bytes) ← decodeUIntLE 1 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (size, bytes) ← decodeUIntLE 4 bytes
  pure ({ nanoseconds, symbolId, tradeId, correctionNumber, price, size }, bytes)

@[simp] theorem encode_length (message : TradeCancelMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : TradeCancelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCancelMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeCancelMessage

/-- Any Data, selected by Message Type -/
inductive Data where
  | systemTimeMessage (message : SystemTimeMessage) -- 49
  | symbolUpdateMessage (message : SymbolUpdateMessage) -- 1
  | systemStateMessage (message : SystemStateMessage) -- 83
  | securityTradingStatusNotificationMessage (message : SecurityTradingStatusNotificationMessage) -- 4
  | symbolClearMessage (message : SymbolClearMessage) -- 5
  | addOrderMessage (message : AddOrderMessage) -- 20
  | modifyOrderMessage (message : ModifyOrderMessage) -- 21
  | deleteOrderMessage (message : DeleteOrderMessage) -- 23
  | orderExecutionMessage (message : OrderExecutionMessage) -- 24
  | tradeMessage (message : TradeMessage) -- 10
  | tradeCancelMessage (message : TradeCancelMessage) -- 11
  deriving DecidableEq, Repr

namespace Data

/-- The Message Type each message is sent under -/
def tag : Data → BitVec 8
  | .systemTimeMessage _ => 49
  | .symbolUpdateMessage _ => 1
  | .systemStateMessage _ => 83
  | .securityTradingStatusNotificationMessage _ => 4
  | .symbolClearMessage _ => 5
  | .addOrderMessage _ => 20
  | .modifyOrderMessage _ => 21
  | .deleteOrderMessage _ => 23
  | .orderExecutionMessage _ => 24
  | .tradeMessage _ => 10
  | .tradeCancelMessage _ => 11

def encode : Data → List UInt8
  | .systemTimeMessage message => SystemTimeMessage.encode message
  | .symbolUpdateMessage message => SymbolUpdateMessage.encode message
  | .systemStateMessage message => SystemStateMessage.encode message
  | .securityTradingStatusNotificationMessage message => SecurityTradingStatusNotificationMessage.encode message
  | .symbolClearMessage message => SymbolClearMessage.encode message
  | .addOrderMessage message => AddOrderMessage.encode message
  | .modifyOrderMessage message => ModifyOrderMessage.encode message
  | .deleteOrderMessage message => DeleteOrderMessage.encode message
  | .orderExecutionMessage message => OrderExecutionMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .tradeCancelMessage message => TradeCancelMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Data) : (encode message).length ≤ 41 := by
  cases message with
  | systemTimeMessage inner =>
    simp only [encode, SystemTimeMessage.encode_length]
    omega
  | symbolUpdateMessage inner =>
    simp only [encode, SymbolUpdateMessage.encode_length]
    omega
  | systemStateMessage inner =>
    simp only [encode, SystemStateMessage.encode_length]
    omega
  | securityTradingStatusNotificationMessage inner =>
    simp only [encode, SecurityTradingStatusNotificationMessage.encode_length]
    omega
  | symbolClearMessage inner =>
    simp only [encode, SymbolClearMessage.encode_length]
    omega
  | addOrderMessage inner =>
    simp only [encode, AddOrderMessage.encode_length]
    omega
  | modifyOrderMessage inner =>
    simp only [encode, ModifyOrderMessage.encode_length]
    omega
  | deleteOrderMessage inner =>
    simp only [encode, DeleteOrderMessage.encode_length]
    omega
  | orderExecutionMessage inner =>
    simp only [encode, OrderExecutionMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [encode, TradeMessage.encode_length]
    omega
  | tradeCancelMessage inner =>
    simp only [encode, TradeCancelMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Data × List UInt8) :=
  if tag = 49 then (SystemTimeMessage.decode bytes).map fun (message, rest) => (.systemTimeMessage message, rest)
  else if tag = 1 then (SymbolUpdateMessage.decode bytes).map fun (message, rest) => (.symbolUpdateMessage message, rest)
  else if tag = 83 then (SystemStateMessage.decode bytes).map fun (message, rest) => (.systemStateMessage message, rest)
  else if tag = 4 then (SecurityTradingStatusNotificationMessage.decode bytes).map fun (message, rest) => (.securityTradingStatusNotificationMessage message, rest)
  else if tag = 5 then (SymbolClearMessage.decode bytes).map fun (message, rest) => (.symbolClearMessage message, rest)
  else if tag = 20 then (AddOrderMessage.decode bytes).map fun (message, rest) => (.addOrderMessage message, rest)
  else if tag = 21 then (ModifyOrderMessage.decode bytes).map fun (message, rest) => (.modifyOrderMessage message, rest)
  else if tag = 23 then (DeleteOrderMessage.decode bytes).map fun (message, rest) => (.deleteOrderMessage message, rest)
  else if tag = 24 then (OrderExecutionMessage.decode bytes).map fun (message, rest) => (.orderExecutionMessage message, rest)
  else if tag = 10 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 11 then (TradeCancelMessage.decode bytes).map fun (message, rest) => (.tradeCancelMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Data) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Data

/-- Application Message -/
structure ApplicationMessage where
  data : Data
  deriving DecidableEq, Repr

namespace ApplicationMessage

def encode (message : ApplicationMessage) : List UInt8 :=
  encodeUInt 1 (Data.tag message.data)
    ++ (Data.encode message.data)

def decode (bytes : List UInt8) : Option (ApplicationMessage × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (data, bytes) ← Data.decode messageType bytes
  pure ({ data }, bytes)

theorem encode_length_pos (message : ApplicationMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ApplicationMessage) : (encode message).length ≤ 42 := by
  unfold encode
  cases message.data with
  | systemTimeMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, SystemTimeMessage.encode_length]
    omega
  | symbolUpdateMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, SymbolUpdateMessage.encode_length]
    omega
  | systemStateMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, SystemStateMessage.encode_length]
    omega
  | securityTradingStatusNotificationMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, SecurityTradingStatusNotificationMessage.encode_length]
    omega
  | symbolClearMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, SymbolClearMessage.encode_length]
    omega
  | addOrderMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, AddOrderMessage.encode_length]
    omega
  | modifyOrderMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, ModifyOrderMessage.encode_length]
    omega
  | deleteOrderMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, DeleteOrderMessage.encode_length]
    omega
  | orderExecutionMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, OrderExecutionMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, TradeMessage.encode_length]
    omega
  | tradeCancelMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, TradeCancelMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : ApplicationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Data.decode_encode, some_bind]
  rfl

end ApplicationMessage

/-- Any Payload, selected by Mach Packet Type -/
inductive Payload where
  | heartbeat (message : Heartbeat) -- 0
  | startOfSession (message : StartOfSession) -- 1
  | endOfSession (message : EndOfSession) -- 2
  | applicationMessage (message : ApplicationMessage) -- 3
  deriving DecidableEq, Repr

namespace Payload

/-- The Mach Packet Type each message is sent under -/
def tag : Payload → BitVec 8
  | .heartbeat _ => 0
  | .startOfSession _ => 1
  | .endOfSession _ => 2
  | .applicationMessage _ => 3

def encode : Payload → List UInt8
  | .heartbeat message => Heartbeat.encode message
  | .startOfSession message => StartOfSession.encode message
  | .endOfSession message => EndOfSession.encode message
  | .applicationMessage message => ApplicationMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 42 := by
  cases message with
  | heartbeat inner =>
    simp only [encode, Heartbeat.encode_length]
    omega
  | startOfSession inner =>
    simp only [encode, StartOfSession.encode_length]
    omega
  | endOfSession inner =>
    simp only [encode, EndOfSession.encode_length]
    omega
  | applicationMessage inner =>
    have bound_inner := ApplicationMessage.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 0 then (Heartbeat.decode bytes).map fun (message, rest) => (.heartbeat message, rest)
  else if tag = 1 then (StartOfSession.decode bytes).map fun (message, rest) => (.startOfSession message, rest)
  else if tag = 2 then (EndOfSession.decode bytes).map fun (message, rest) => (.endOfSession message, rest)
  else if tag = 3 then (ApplicationMessage.decode bytes).map fun (message, rest) => (.applicationMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Mach Message -/
structure MachMessage where
  sequenceNumber : BitVec 64
  machPacketLength : BitVec 16
  sessionNumber : BitVec 8
  payload : Payload
  deriving DecidableEq, Repr

namespace MachMessage

def encode (message : MachMessage) : List UInt8 :=
  encodeUIntLE 8 message.sequenceNumber
    ++ (encodeUIntLE 2 message.machPacketLength
    ++ (encodeUIntLE 1 (Payload.tag message.payload)
    ++ (encodeUIntLE 1 message.sessionNumber
    ++ (Payload.encode message.payload))))

def decode (bytes : List UInt8) : Option (MachMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 8 bytes
  let (machPacketLength, bytes) ← decodeUIntLE 2 bytes
  let (machPacketType, bytes) ← decodeUIntLE 1 bytes
  let (sessionNumber, bytes) ← decodeUIntLE 1 bytes
  let (payload, bytes) ← Payload.decode machPacketType bytes
  pure ({ sequenceNumber, machPacketLength, sessionNumber, payload }, bytes)

theorem encode_length_pos (message : MachMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MachMessage) : (encode message).length ≤ 54 := by
  unfold encode
  cases message.payload with
  | heartbeat inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Heartbeat.encode_length]
    omega
  | startOfSession inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, StartOfSession.encode_length]
    omega
  | endOfSession inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, EndOfSession.encode_length]
    omega
  | applicationMessage inner =>
    have bound_inner := ApplicationMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega

@[simp] theorem decode_encode (message : MachMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

end MachMessage

/-- Packet -/
structure Packet where
  machMessage : List MachMessage
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeMany MachMessage.encode message.machMessage

def decode (bytes : List UInt8) : Option Packet := do
  let machMessage ← decodeAll MachMessage.decode bytes.length bytes
  pure { machMessage }

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany MachMessage.encode MachMessage.decode MachMessage.decode_encode MachMessage.encode_length_pos message.machMessage _ (encodeMany_length_ge MachMessage.encode MachMessage.encode_length_pos message.machMessage), some_bind]
  rfl

end Packet

end Omi.MiaxPearlequitiesDepthofmarketMachV13A
