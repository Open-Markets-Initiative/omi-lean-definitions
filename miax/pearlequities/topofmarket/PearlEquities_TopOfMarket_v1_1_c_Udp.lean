import Omi.Wire

/-!
# Miami International Holdings Top Of Market v1.1.c

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Application Message is not framed: its length Mach Packet Length is not an integer it reads.

Note: Udp Packet is not framed: its length Mach Packet Length is not an integer it reads.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.MiaxPearlequitiesTopofmarketMachV11CUdp

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
  [0x41, 0x42, 0x43, 0x46, 0x47, 0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x50, 0x51, 0x55, 0x56, 0x57, 0x58, 0x59, 0x5A]

inductive PrimaryMarketCode where
  | nyseAmerican -- Nyse American
  | nasdaqTexas -- Nasdaq Texas
  | nyseNational -- Nyse National
  | texasStockExchange -- Texas Stock Exchange
  | n24XExchange -- N 24 X Exchange
  | miaxPearlEquities -- Miax Pearl Equities
  | nasdaqIse -- Nasdaq Ise
  | cboeEdgaExchange -- Cboe Edga Exchange
  | cboeEdgxExchange -- Cboe Edgx Exchange
  | longTermStockExchange -- Long Term Stock Exchange
  | nyseTexas -- Nyse Texas
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
  | .nasdaqTexas => 0x42
  | .nyseNational => 0x43
  | .texasStockExchange => 0x46
  | .n24XExchange => 0x47
  | .miaxPearlEquities => 0x48
  | .nasdaqIse => 0x49
  | .cboeEdgaExchange => 0x4A
  | .cboeEdgxExchange => 0x4B
  | .longTermStockExchange => 0x4C
  | .nyseTexas => 0x4D
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
  else if byte = 0x42 then .nasdaqTexas
  else if byte = 0x43 then .nyseNational
  else if byte = 0x46 then .texasStockExchange
  else if byte = 0x47 then .n24XExchange
  else if byte = 0x48 then .miaxPearlEquities
  else if byte = 0x49 then .nasdaqIse
  else if byte = 0x4A then .cboeEdgaExchange
  else if byte = 0x4B then .cboeEdgxExchange
  else if byte = 0x4C then .longTermStockExchange
  else if byte = 0x4D then .nyseTexas
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
  | nasdaqTexas => decide
  | nyseNational => decide
  | texasStockExchange => decide
  | n24XExchange => decide
  | miaxPearlEquities => decide
  | nasdaqIse => decide
  | cboeEdgaExchange => decide
  | cboeEdgxExchange => decide
  | longTermStockExchange => decide
  | nyseTexas => decide
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
  | shortSaleRestrictionIsInEffect -- Short Sale Restriction Is In Effect
  | shortSaleRestrictionIsNotInEffect -- Short Sale Restriction Is Not In Effect
  | unlisted (byte : { byte : UInt8 // byte ∉ ShortSaleRestriction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ShortSaleRestriction

def toByte : ShortSaleRestriction → UInt8
  | .shortSaleRestrictionIsInEffect => 0x59
  | .shortSaleRestrictionIsNotInEffect => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ShortSaleRestriction :=
  if byte = 0x59 then .shortSaleRestrictionIsInEffect
  else .shortSaleRestrictionIsNotInEffect

def ofByte (byte : UInt8) : ShortSaleRestriction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ShortSaleRestriction) : ofByte value.toByte = value := by
  cases value with
  | shortSaleRestrictionIsInEffect => decide
  | shortSaleRestrictionIsNotInEffect => decide
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
  secondReserved1 : Alpha 1
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
    ++ (Alpha.encode message.secondReserved1
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
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (lotSize, bytes) ← decodeUIntLE 2 bytes
  let (openingTime, bytes) ← Alpha.decode 8 bytes
  let (closingTime, bytes) ← Alpha.decode 8 bytes
  let (primaryMarketCode, bytes) ← PrimaryMarketCode.decode bytes
  pure ({ nanoseconds, symbolId, tickerSymbol, reserved1, testSecurityIndicator, secondReserved1, lotSize, openingTime, closingTime, primaryMarketCode }, bytes)

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  toMVersion : Alpha 8
  sessionId : BitVec 8
  systemStatus : SystemStatus
  deriving DecidableEq, Repr

namespace SystemStateMessage

def encode (message : SystemStateMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (Alpha.encode message.toMVersion
    ++ (encodeUIntLE 1 message.sessionId
    ++ (SystemStatus.encode message.systemStatus)))

def decode (bytes : List UInt8) : Option (SystemStateMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (toMVersion, bytes) ← Alpha.decode 8 bytes
  let (sessionId, bytes) ← decodeUIntLE 1 bytes
  let (systemStatus, bytes) ← SystemStatus.decode bytes
  pure ({ nanoseconds, toMVersion, sessionId, systemStatus }, bytes)

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

/-- Compact Top Of Market Best Bid And Offer Message: 16 bytes -/
structure CompactTopOfMarketBestBidAndOfferMessage where
  nanoseconds : BitVec 32
  symbolId : BitVec 32
  bidPriceShort : BitVec 16
  bidSizeShort : BitVec 16
  offerPriceShort : BitVec 16
  offerSizeShort : BitVec 16
  deriving DecidableEq, Repr

namespace CompactTopOfMarketBestBidAndOfferMessage

def encode (message : CompactTopOfMarketBestBidAndOfferMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.symbolId
    ++ (encodeUIntLE 2 message.bidPriceShort
    ++ (encodeUIntLE 2 message.bidSizeShort
    ++ (encodeUIntLE 2 message.offerPriceShort
    ++ (encodeUIntLE 2 message.offerSizeShort)))))

def decode (bytes : List UInt8) : Option (CompactTopOfMarketBestBidAndOfferMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (bidPriceShort, bytes) ← decodeUIntLE 2 bytes
  let (bidSizeShort, bytes) ← decodeUIntLE 2 bytes
  let (offerPriceShort, bytes) ← decodeUIntLE 2 bytes
  let (offerSizeShort, bytes) ← decodeUIntLE 2 bytes
  pure ({ nanoseconds, symbolId, bidPriceShort, bidSizeShort, offerPriceShort, offerSizeShort }, bytes)

@[simp] theorem encode_length (message : CompactTopOfMarketBestBidAndOfferMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : CompactTopOfMarketBestBidAndOfferMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CompactTopOfMarketBestBidAndOfferMessage) (rest : List UInt8) :
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

end CompactTopOfMarketBestBidAndOfferMessage

/-- Wide Top Of Market Best Bid And Offer Message: 32 bytes -/
structure WideTopOfMarketBestBidAndOfferMessage where
  nanoseconds : BitVec 32
  symbolId : BitVec 32
  bidPriceLong : BitVec 64
  bidSizeLong : BitVec 32
  offerPriceLong : BitVec 64
  offerSizeLong : BitVec 32
  deriving DecidableEq, Repr

namespace WideTopOfMarketBestBidAndOfferMessage

def encode (message : WideTopOfMarketBestBidAndOfferMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.symbolId
    ++ (encodeUIntLE 8 message.bidPriceLong
    ++ (encodeUIntLE 4 message.bidSizeLong
    ++ (encodeUIntLE 8 message.offerPriceLong
    ++ (encodeUIntLE 4 message.offerSizeLong)))))

def decode (bytes : List UInt8) : Option (WideTopOfMarketBestBidAndOfferMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (bidPriceLong, bytes) ← decodeUIntLE 8 bytes
  let (bidSizeLong, bytes) ← decodeUIntLE 4 bytes
  let (offerPriceLong, bytes) ← decodeUIntLE 8 bytes
  let (offerSizeLong, bytes) ← decodeUIntLE 4 bytes
  pure ({ nanoseconds, symbolId, bidPriceLong, bidSizeLong, offerPriceLong, offerSizeLong }, bytes)

@[simp] theorem encode_length (message : WideTopOfMarketBestBidAndOfferMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : WideTopOfMarketBestBidAndOfferMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : WideTopOfMarketBestBidAndOfferMessage) (rest : List UInt8) :
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

end WideTopOfMarketBestBidAndOfferMessage

/-- Last Sale Message: 30 bytes -/
structure LastSaleMessage where
  nanoseconds : BitVec 32
  symbolId : BitVec 32
  tradeId : BitVec 64
  correctionNumber : BitVec 8
  price : BitVec 64
  size : BitVec 32
  flags : BitVec 8
  deriving DecidableEq, Repr

namespace LastSaleMessage

def encode (message : LastSaleMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanoseconds
    ++ (encodeUIntLE 4 message.symbolId
    ++ (encodeUIntLE 8 message.tradeId
    ++ (encodeUIntLE 1 message.correctionNumber
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.size
    ++ (encodeUIntLE 1 message.flags))))))

def decode (bytes : List UInt8) : Option (LastSaleMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  let (symbolId, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 8 bytes
  let (correctionNumber, bytes) ← decodeUIntLE 1 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (size, bytes) ← decodeUIntLE 4 bytes
  let (flags, bytes) ← decodeUIntLE 1 bytes
  pure ({ nanoseconds, symbolId, tradeId, correctionNumber, price, size, flags }, bytes)

@[simp] theorem encode_length (message : LastSaleMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : LastSaleMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LastSaleMessage) (rest : List UInt8) :
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

end LastSaleMessage

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
  | compactTopOfMarketBestBidAndOfferMessage (message : CompactTopOfMarketBestBidAndOfferMessage) -- 2
  | wideTopOfMarketBestBidAndOfferMessage (message : WideTopOfMarketBestBidAndOfferMessage) -- 3
  | lastSaleMessage (message : LastSaleMessage) -- 10
  | tradeCancelMessage (message : TradeCancelMessage) -- 11
  deriving DecidableEq, Repr

namespace Data

/-- The Message Type each message is sent under -/
def tag : Data → BitVec 8
  | .systemTimeMessage _ => 49
  | .symbolUpdateMessage _ => 1
  | .systemStateMessage _ => 83
  | .securityTradingStatusNotificationMessage _ => 4
  | .compactTopOfMarketBestBidAndOfferMessage _ => 2
  | .wideTopOfMarketBestBidAndOfferMessage _ => 3
  | .lastSaleMessage _ => 10
  | .tradeCancelMessage _ => 11

def encode : Data → List UInt8
  | .systemTimeMessage message => SystemTimeMessage.encode message
  | .symbolUpdateMessage message => SymbolUpdateMessage.encode message
  | .systemStateMessage message => SystemStateMessage.encode message
  | .securityTradingStatusNotificationMessage message => SecurityTradingStatusNotificationMessage.encode message
  | .compactTopOfMarketBestBidAndOfferMessage message => CompactTopOfMarketBestBidAndOfferMessage.encode message
  | .wideTopOfMarketBestBidAndOfferMessage message => WideTopOfMarketBestBidAndOfferMessage.encode message
  | .lastSaleMessage message => LastSaleMessage.encode message
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
  | compactTopOfMarketBestBidAndOfferMessage inner =>
    simp only [encode, CompactTopOfMarketBestBidAndOfferMessage.encode_length]
    omega
  | wideTopOfMarketBestBidAndOfferMessage inner =>
    simp only [encode, WideTopOfMarketBestBidAndOfferMessage.encode_length]
    omega
  | lastSaleMessage inner =>
    simp only [encode, LastSaleMessage.encode_length]
    omega
  | tradeCancelMessage inner =>
    simp only [encode, TradeCancelMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Data × List UInt8) :=
  if tag = 49 then (SystemTimeMessage.decode bytes).map fun (message, rest) => (.systemTimeMessage message, rest)
  else if tag = 1 then (SymbolUpdateMessage.decode bytes).map fun (message, rest) => (.symbolUpdateMessage message, rest)
  else if tag = 83 then (SystemStateMessage.decode bytes).map fun (message, rest) => (.systemStateMessage message, rest)
  else if tag = 4 then (SecurityTradingStatusNotificationMessage.decode bytes).map fun (message, rest) => (.securityTradingStatusNotificationMessage message, rest)
  else if tag = 2 then (CompactTopOfMarketBestBidAndOfferMessage.decode bytes).map fun (message, rest) => (.compactTopOfMarketBestBidAndOfferMessage message, rest)
  else if tag = 3 then (WideTopOfMarketBestBidAndOfferMessage.decode bytes).map fun (message, rest) => (.wideTopOfMarketBestBidAndOfferMessage message, rest)
  else if tag = 10 then (LastSaleMessage.decode bytes).map fun (message, rest) => (.lastSaleMessage message, rest)
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
  | compactTopOfMarketBestBidAndOfferMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, CompactTopOfMarketBestBidAndOfferMessage.encode_length]
    omega
  | wideTopOfMarketBestBidAndOfferMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, WideTopOfMarketBestBidAndOfferMessage.encode_length]
    omega
  | lastSaleMessage inner =>
    simp only [Data.encode, List.length_append, encodeUInt_length, LastSaleMessage.encode_length]
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

/-- Udp Packet -/
structure UdpPacket where
  machMessage : List MachMessage
  deriving DecidableEq, Repr

namespace UdpPacket

def encode (message : UdpPacket) : List UInt8 :=
  encodeMany MachMessage.encode message.machMessage

def decode (bytes : List UInt8) : Option UdpPacket := do
  let machMessage ← decodeAll MachMessage.decode bytes.length bytes
  pure { machMessage }

theorem decode_encode (message : UdpPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany MachMessage.encode MachMessage.decode MachMessage.decode_encode MachMessage.encode_length_pos message.machMessage _ (encodeMany_length_ge MachMessage.encode MachMessage.encode_length_pos message.machMessage), some_bind]
  rfl

end UdpPacket

end Omi.MiaxPearlequitiesTopofmarketMachV11CUdp
