import Omi.Wire

/-!
# CME Group Derived Market Data v12.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Match Event Indicator is a bit field set, proven as its 1 byte integer rather than bit by bit.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.CmeGlobexDerivedSbeV120Tcp

/-- Md Entry Type Spectrum Entry Type: one byte code -/
def MdEntryTypeSpectrumEntryType.codes : List UInt8 :=
  [0x39, 0x74]

inductive MdEntryTypeSpectrumEntryType where
  | vwap -- Vwap
  | twap -- Twap
  | unlisted (byte : { byte : UInt8 // byte ∉ MdEntryTypeSpectrumEntryType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MdEntryTypeSpectrumEntryType

def toByte : MdEntryTypeSpectrumEntryType → UInt8
  | .vwap => 0x39
  | .twap => 0x74
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MdEntryTypeSpectrumEntryType :=
  if byte = 0x39 then .vwap
  else .twap

def ofByte (byte : UInt8) : MdEntryTypeSpectrumEntryType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MdEntryTypeSpectrumEntryType) : ofByte value.toByte = value := by
  cases value with
  | vwap => decide
  | twap => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MdEntryTypeSpectrumEntryType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MdEntryTypeSpectrumEntryType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MdEntryTypeSpectrumEntryType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MdEntryTypeSpectrumEntryType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MdEntryTypeSpectrumEntryType

/-- Md Entry Type Ticker Entry Type: one byte code -/
def MdEntryTypeTickerEntryType.codes : List UInt8 :=
  [0x6B, 0x6C, 0x6D, 0x6E, 0x6F, 0x70, 0x71, 0x72, 0x77, 0x78, 0x79, 0x7A]

inductive MdEntryTypeTickerEntryType where
  | touchHigh -- Touch High
  | touchLow -- Touch Low
  | openBestBid -- Open Best Bid
  | openBestOffer -- Open Best Offer
  | closeBestBid -- Close Best Bid
  | closeBestOffer -- Close Best Offer
  | marketHigh -- Market High
  | marketLow -- Market Low
  | marketBestOffer -- Market Best Offer
  | marketBestBid -- Market Best Bid
  | paid -- Paid
  | given -- Given
  | unlisted (byte : { byte : UInt8 // byte ∉ MdEntryTypeTickerEntryType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MdEntryTypeTickerEntryType

def toByte : MdEntryTypeTickerEntryType → UInt8
  | .touchHigh => 0x6B
  | .touchLow => 0x6C
  | .openBestBid => 0x6D
  | .openBestOffer => 0x6E
  | .closeBestBid => 0x6F
  | .closeBestOffer => 0x70
  | .marketHigh => 0x71
  | .marketLow => 0x72
  | .marketBestOffer => 0x77
  | .marketBestBid => 0x78
  | .paid => 0x79
  | .given => 0x7A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MdEntryTypeTickerEntryType :=
  if byte = 0x6B then .touchHigh
  else if byte = 0x6C then .touchLow
  else if byte = 0x6D then .openBestBid
  else if byte = 0x6E then .openBestOffer
  else if byte = 0x6F then .closeBestBid
  else if byte = 0x70 then .closeBestOffer
  else if byte = 0x71 then .marketHigh
  else if byte = 0x72 then .marketLow
  else if byte = 0x77 then .marketBestOffer
  else if byte = 0x78 then .marketBestBid
  else if byte = 0x79 then .paid
  else .given

def ofByte (byte : UInt8) : MdEntryTypeTickerEntryType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MdEntryTypeTickerEntryType) : ofByte value.toByte = value := by
  cases value with
  | touchHigh => decide
  | touchLow => decide
  | openBestBid => decide
  | openBestOffer => decide
  | closeBestBid => decide
  | closeBestOffer => decide
  | marketHigh => decide
  | marketLow => decide
  | marketBestOffer => decide
  | marketBestBid => decide
  | paid => decide
  | given => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MdEntryTypeTickerEntryType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MdEntryTypeTickerEntryType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MdEntryTypeTickerEntryType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MdEntryTypeTickerEntryType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MdEntryTypeTickerEntryType

/-- Technical Header: 14 bytes -/
structure TechnicalHeader where
  encodingType : BitVec 16
  messageSequenceNumber : BitVec 32
  tcpSendingTime : BitVec 64
  deriving DecidableEq, Repr

namespace TechnicalHeader

def encode (message : TechnicalHeader) : List UInt8 :=
  encodeUIntLE 2 message.encodingType
    ++ encodeUIntLE 4 message.messageSequenceNumber
    ++ encodeUIntLE 8 message.tcpSendingTime

def decode (bytes : List UInt8) : Option (TechnicalHeader × List UInt8) := do
  let (encodingType, bytes) ← decodeUIntLE 2 bytes
  let (messageSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (tcpSendingTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ encodingType, messageSequenceNumber, tcpSendingTime }, bytes)

@[simp] theorem encode_length (message : TechnicalHeader) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : TechnicalHeader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TechnicalHeader) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end TechnicalHeader

/-- Admin Heartbeat: 0 bytes -/
structure AdminHeartbeat where
  deriving DecidableEq, Repr

namespace AdminHeartbeat

def encode (_ : AdminHeartbeat) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (AdminHeartbeat × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : AdminHeartbeat) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : AdminHeartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end AdminHeartbeat

/-- Incremental Refresh Spectrum Group: 92 bytes -/
structure IncrementalRefreshSpectrumGroup where
  mdEntryTypeSpectrumEntryType : MdEntryTypeSpectrumEntryType
  financialInstrumentFullName : Alpha 35
  symbol : Alpha 20
  instrumentGuid : BitVec 64
  securityId : BitVec 32
  mdEntryPx : BitVec 64
  mdEntrySize : BitVec 64
  mdEntryTime : BitVec 64
  deriving DecidableEq, Repr

namespace IncrementalRefreshSpectrumGroup

def encode (message : IncrementalRefreshSpectrumGroup) : List UInt8 :=
  MdEntryTypeSpectrumEntryType.encode message.mdEntryTypeSpectrumEntryType
    ++ Alpha.encode message.financialInstrumentFullName
    ++ Alpha.encode message.symbol
    ++ encodeUIntLE 8 message.instrumentGuid
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 8 message.mdEntryPx
    ++ encodeUIntLE 8 message.mdEntrySize
    ++ encodeUIntLE 8 message.mdEntryTime

def decode (bytes : List UInt8) : Option (IncrementalRefreshSpectrumGroup × List UInt8) := do
  let (mdEntryTypeSpectrumEntryType, bytes) ← MdEntryTypeSpectrumEntryType.decode bytes
  let (financialInstrumentFullName, bytes) ← Alpha.decode 35 bytes
  let (symbol, bytes) ← Alpha.decode 20 bytes
  let (instrumentGuid, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (mdEntryPx, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySize, bytes) ← decodeUIntLE 8 bytes
  let (mdEntryTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ mdEntryTypeSpectrumEntryType, financialInstrumentFullName, symbol, instrumentGuid, securityId, mdEntryPx, mdEntrySize, mdEntryTime }, bytes)

@[simp] theorem encode_length (message : IncrementalRefreshSpectrumGroup) : (encode message).length = 92 := by
  unfold encode
  simp only [List.length_append, MdEntryTypeSpectrumEntryType.encode_length, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : IncrementalRefreshSpectrumGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IncrementalRefreshSpectrumGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [MdEntryTypeSpectrumEntryType.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end IncrementalRefreshSpectrumGroup

/-- Incremental Refresh Spectrum Groups -/
structure IncrementalRefreshSpectrumGroups where
  blockLength : BitVec 16
  incrementalRefreshSpectrumGroup : Bounded 1 IncrementalRefreshSpectrumGroup
  deriving DecidableEq, Repr

namespace IncrementalRefreshSpectrumGroups

def encode (message : IncrementalRefreshSpectrumGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.incrementalRefreshSpectrumGroup.val.length)
    ++ encodeMany IncrementalRefreshSpectrumGroup.encode message.incrementalRefreshSpectrumGroup.val

def decode (bytes : List UInt8) : Option (IncrementalRefreshSpectrumGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshSpectrumGroup_, bytes) ← decodeMany IncrementalRefreshSpectrumGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshSpectrumGroup : incrementalRefreshSpectrumGroup_.length < 256 ^ 1 then
    pure ({ blockLength, incrementalRefreshSpectrumGroup := ⟨incrementalRefreshSpectrumGroup_, fits_incrementalRefreshSpectrumGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : IncrementalRefreshSpectrumGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : IncrementalRefreshSpectrumGroups) : (encode message).length ≤ 23463 := by
  have bound_incrementalRefreshSpectrumGroup := message.incrementalRefreshSpectrumGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const IncrementalRefreshSpectrumGroup.encode 92 IncrementalRefreshSpectrumGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : IncrementalRefreshSpectrumGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeMany_bounded 1 IncrementalRefreshSpectrumGroup.encode IncrementalRefreshSpectrumGroup.decode IncrementalRefreshSpectrumGroup.decode_encode, Option.bind_some]
  dsimp only
  simp only [message.incrementalRefreshSpectrumGroup.length_lt, ↓reduceDIte]
  rfl

end IncrementalRefreshSpectrumGroups

/-- Md Incremental Refresh Spectrum -/
structure MdIncrementalRefreshSpectrum where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  incrementalRefreshSpectrumGroups : IncrementalRefreshSpectrumGroups
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshSpectrum

def encode (message : MdIncrementalRefreshSpectrum) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ IncrementalRefreshSpectrumGroups.encode message.incrementalRefreshSpectrumGroups

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshSpectrum × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (incrementalRefreshSpectrumGroups, bytes) ← IncrementalRefreshSpectrumGroups.decode bytes
  pure ({ transactTime, matchEventIndicator, incrementalRefreshSpectrumGroups }, bytes)

theorem encode_length_pos (message : MdIncrementalRefreshSpectrum) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdIncrementalRefreshSpectrum) : (encode message).length ≤ 23472 := by
  have bound_incrementalRefreshSpectrumGroups := IncrementalRefreshSpectrumGroups.encode_length_le message.incrementalRefreshSpectrumGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]
  omega

@[simp] theorem decode_encode (message : MdIncrementalRefreshSpectrum) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [IncrementalRefreshSpectrumGroups.decode_encode, Option.bind_some]
  rfl

end MdIncrementalRefreshSpectrum

/-- Incremental Refresh Ticker Group: 95 bytes -/
structure IncrementalRefreshTickerGroup where
  mdEntryTypeTickerEntryType : MdEntryTypeTickerEntryType
  securityId : BitVec 32
  symbol : Alpha 20
  instrumentGuid : BitVec 64
  financialInstrumentFullName : Alpha 35
  mdEntryPx : BitVec 64
  mdEntrySize : BitVec 64
  mdEntryTime : BitVec 64
  openCloseSettlFlag : BitVec 8
  tradingSessionId : BitVec 8
  aggressorSide : BitVec 8
  deriving DecidableEq, Repr

namespace IncrementalRefreshTickerGroup

def encode (message : IncrementalRefreshTickerGroup) : List UInt8 :=
  MdEntryTypeTickerEntryType.encode message.mdEntryTypeTickerEntryType
    ++ encodeUIntLE 4 message.securityId
    ++ Alpha.encode message.symbol
    ++ encodeUIntLE 8 message.instrumentGuid
    ++ Alpha.encode message.financialInstrumentFullName
    ++ encodeUIntLE 8 message.mdEntryPx
    ++ encodeUIntLE 8 message.mdEntrySize
    ++ encodeUIntLE 8 message.mdEntryTime
    ++ encodeUInt 1 message.openCloseSettlFlag
    ++ encodeUInt 1 message.tradingSessionId
    ++ encodeUInt 1 message.aggressorSide

def decode (bytes : List UInt8) : Option (IncrementalRefreshTickerGroup × List UInt8) := do
  let (mdEntryTypeTickerEntryType, bytes) ← MdEntryTypeTickerEntryType.decode bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (symbol, bytes) ← Alpha.decode 20 bytes
  let (instrumentGuid, bytes) ← decodeUIntLE 8 bytes
  let (financialInstrumentFullName, bytes) ← Alpha.decode 35 bytes
  let (mdEntryPx, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySize, bytes) ← decodeUIntLE 8 bytes
  let (mdEntryTime, bytes) ← decodeUIntLE 8 bytes
  let (openCloseSettlFlag, bytes) ← decodeUInt 1 bytes
  let (tradingSessionId, bytes) ← decodeUInt 1 bytes
  let (aggressorSide, bytes) ← decodeUInt 1 bytes
  pure ({ mdEntryTypeTickerEntryType, securityId, symbol, instrumentGuid, financialInstrumentFullName, mdEntryPx, mdEntrySize, mdEntryTime, openCloseSettlFlag, tradingSessionId, aggressorSide }, bytes)

@[simp] theorem encode_length (message : IncrementalRefreshTickerGroup) : (encode message).length = 95 := by
  unfold encode
  simp only [List.length_append, MdEntryTypeTickerEntryType.encode_length, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : IncrementalRefreshTickerGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IncrementalRefreshTickerGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [MdEntryTypeTickerEntryType.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end IncrementalRefreshTickerGroup

/-- Incremental Refresh Ticker Groups -/
structure IncrementalRefreshTickerGroups where
  blockLength : BitVec 16
  incrementalRefreshTickerGroup : Bounded 1 IncrementalRefreshTickerGroup
  deriving DecidableEq, Repr

namespace IncrementalRefreshTickerGroups

def encode (message : IncrementalRefreshTickerGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.incrementalRefreshTickerGroup.val.length)
    ++ encodeMany IncrementalRefreshTickerGroup.encode message.incrementalRefreshTickerGroup.val

def decode (bytes : List UInt8) : Option (IncrementalRefreshTickerGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshTickerGroup_, bytes) ← decodeMany IncrementalRefreshTickerGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshTickerGroup : incrementalRefreshTickerGroup_.length < 256 ^ 1 then
    pure ({ blockLength, incrementalRefreshTickerGroup := ⟨incrementalRefreshTickerGroup_, fits_incrementalRefreshTickerGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : IncrementalRefreshTickerGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : IncrementalRefreshTickerGroups) : (encode message).length ≤ 24228 := by
  have bound_incrementalRefreshTickerGroup := message.incrementalRefreshTickerGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const IncrementalRefreshTickerGroup.encode 95 IncrementalRefreshTickerGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : IncrementalRefreshTickerGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeMany_bounded 1 IncrementalRefreshTickerGroup.encode IncrementalRefreshTickerGroup.decode IncrementalRefreshTickerGroup.decode_encode, Option.bind_some]
  dsimp only
  simp only [message.incrementalRefreshTickerGroup.length_lt, ↓reduceDIte]
  rfl

end IncrementalRefreshTickerGroups

/-- Md Incremental Refresh Ticker -/
structure MdIncrementalRefreshTicker where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  incrementalRefreshTickerGroups : IncrementalRefreshTickerGroups
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshTicker

def encode (message : MdIncrementalRefreshTicker) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ IncrementalRefreshTickerGroups.encode message.incrementalRefreshTickerGroups

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshTicker × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (incrementalRefreshTickerGroups, bytes) ← IncrementalRefreshTickerGroups.decode bytes
  pure ({ transactTime, matchEventIndicator, incrementalRefreshTickerGroups }, bytes)

theorem encode_length_pos (message : MdIncrementalRefreshTicker) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdIncrementalRefreshTicker) : (encode message).length ≤ 24237 := by
  have bound_incrementalRefreshTickerGroups := IncrementalRefreshTickerGroups.encode_length_le message.incrementalRefreshTickerGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]
  omega

@[simp] theorem decode_encode (message : MdIncrementalRefreshTicker) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [IncrementalRefreshTickerGroups.decode_encode, Option.bind_some]
  rfl

end MdIncrementalRefreshTicker

/-- Snapshot Refresh Spectrum Group: 25 bytes -/
structure SnapshotRefreshSpectrumGroup where
  mdEntryTypeSpectrumEntryType : MdEntryTypeSpectrumEntryType
  mdEntryPx : BitVec 64
  mdEntrySize : BitVec 64
  mdEntryTime : BitVec 64
  deriving DecidableEq, Repr

namespace SnapshotRefreshSpectrumGroup

def encode (message : SnapshotRefreshSpectrumGroup) : List UInt8 :=
  MdEntryTypeSpectrumEntryType.encode message.mdEntryTypeSpectrumEntryType
    ++ encodeUIntLE 8 message.mdEntryPx
    ++ encodeUIntLE 8 message.mdEntrySize
    ++ encodeUIntLE 8 message.mdEntryTime

def decode (bytes : List UInt8) : Option (SnapshotRefreshSpectrumGroup × List UInt8) := do
  let (mdEntryTypeSpectrumEntryType, bytes) ← MdEntryTypeSpectrumEntryType.decode bytes
  let (mdEntryPx, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySize, bytes) ← decodeUIntLE 8 bytes
  let (mdEntryTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ mdEntryTypeSpectrumEntryType, mdEntryPx, mdEntrySize, mdEntryTime }, bytes)

@[simp] theorem encode_length (message : SnapshotRefreshSpectrumGroup) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, MdEntryTypeSpectrumEntryType.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : SnapshotRefreshSpectrumGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SnapshotRefreshSpectrumGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [MdEntryTypeSpectrumEntryType.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end SnapshotRefreshSpectrumGroup

/-- Snapshot Refresh Spectrum Groups -/
structure SnapshotRefreshSpectrumGroups where
  blockLength : BitVec 16
  snapshotRefreshSpectrumGroup : Bounded 1 SnapshotRefreshSpectrumGroup
  deriving DecidableEq, Repr

namespace SnapshotRefreshSpectrumGroups

def encode (message : SnapshotRefreshSpectrumGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.snapshotRefreshSpectrumGroup.val.length)
    ++ encodeMany SnapshotRefreshSpectrumGroup.encode message.snapshotRefreshSpectrumGroup.val

def decode (bytes : List UInt8) : Option (SnapshotRefreshSpectrumGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (snapshotRefreshSpectrumGroup_, bytes) ← decodeMany SnapshotRefreshSpectrumGroup.decode numInGroup.toNat bytes
  if fits_snapshotRefreshSpectrumGroup : snapshotRefreshSpectrumGroup_.length < 256 ^ 1 then
    pure ({ blockLength, snapshotRefreshSpectrumGroup := ⟨snapshotRefreshSpectrumGroup_, fits_snapshotRefreshSpectrumGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : SnapshotRefreshSpectrumGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SnapshotRefreshSpectrumGroups) : (encode message).length ≤ 6378 := by
  have bound_snapshotRefreshSpectrumGroup := message.snapshotRefreshSpectrumGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const SnapshotRefreshSpectrumGroup.encode 25 SnapshotRefreshSpectrumGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : SnapshotRefreshSpectrumGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeMany_bounded 1 SnapshotRefreshSpectrumGroup.encode SnapshotRefreshSpectrumGroup.decode SnapshotRefreshSpectrumGroup.decode_encode, Option.bind_some]
  dsimp only
  simp only [message.snapshotRefreshSpectrumGroup.length_lt, ↓reduceDIte]
  rfl

end SnapshotRefreshSpectrumGroups

/-- Md Snapshot Refresh Spectrum -/
structure MdSnapshotRefreshSpectrum where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  financialInstrumentFullName : Alpha 35
  symbol : Alpha 20
  instrumentGuid : BitVec 64
  securityId : BitVec 32
  snapshotRefreshSpectrumGroups : SnapshotRefreshSpectrumGroups
  deriving DecidableEq, Repr

namespace MdSnapshotRefreshSpectrum

def encode (message : MdSnapshotRefreshSpectrum) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ Alpha.encode message.financialInstrumentFullName
    ++ Alpha.encode message.symbol
    ++ encodeUIntLE 8 message.instrumentGuid
    ++ encodeUIntLE 4 message.securityId
    ++ SnapshotRefreshSpectrumGroups.encode message.snapshotRefreshSpectrumGroups

def decode (bytes : List UInt8) : Option (MdSnapshotRefreshSpectrum × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (financialInstrumentFullName, bytes) ← Alpha.decode 35 bytes
  let (symbol, bytes) ← Alpha.decode 20 bytes
  let (instrumentGuid, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (snapshotRefreshSpectrumGroups, bytes) ← SnapshotRefreshSpectrumGroups.decode bytes
  pure ({ transactTime, matchEventIndicator, financialInstrumentFullName, symbol, instrumentGuid, securityId, snapshotRefreshSpectrumGroups }, bytes)

theorem encode_length_pos (message : MdSnapshotRefreshSpectrum) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdSnapshotRefreshSpectrum) : (encode message).length ≤ 6454 := by
  have bound_snapshotRefreshSpectrumGroups := SnapshotRefreshSpectrumGroups.encode_length_le message.snapshotRefreshSpectrumGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : MdSnapshotRefreshSpectrum) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [SnapshotRefreshSpectrumGroups.decode_encode, Option.bind_some]
  rfl

end MdSnapshotRefreshSpectrum

/-- Snapshot Refresh Ticker Group: 28 bytes -/
structure SnapshotRefreshTickerGroup where
  mdEntryTypeTickerEntryType : MdEntryTypeTickerEntryType
  mdEntryPx : BitVec 64
  mdEntrySize : BitVec 64
  mdEntryTime : BitVec 64
  openCloseSettlFlag : BitVec 8
  tradingSessionId : BitVec 8
  aggressorSide : BitVec 8
  deriving DecidableEq, Repr

namespace SnapshotRefreshTickerGroup

def encode (message : SnapshotRefreshTickerGroup) : List UInt8 :=
  MdEntryTypeTickerEntryType.encode message.mdEntryTypeTickerEntryType
    ++ encodeUIntLE 8 message.mdEntryPx
    ++ encodeUIntLE 8 message.mdEntrySize
    ++ encodeUIntLE 8 message.mdEntryTime
    ++ encodeUInt 1 message.openCloseSettlFlag
    ++ encodeUInt 1 message.tradingSessionId
    ++ encodeUInt 1 message.aggressorSide

def decode (bytes : List UInt8) : Option (SnapshotRefreshTickerGroup × List UInt8) := do
  let (mdEntryTypeTickerEntryType, bytes) ← MdEntryTypeTickerEntryType.decode bytes
  let (mdEntryPx, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySize, bytes) ← decodeUIntLE 8 bytes
  let (mdEntryTime, bytes) ← decodeUIntLE 8 bytes
  let (openCloseSettlFlag, bytes) ← decodeUInt 1 bytes
  let (tradingSessionId, bytes) ← decodeUInt 1 bytes
  let (aggressorSide, bytes) ← decodeUInt 1 bytes
  pure ({ mdEntryTypeTickerEntryType, mdEntryPx, mdEntrySize, mdEntryTime, openCloseSettlFlag, tradingSessionId, aggressorSide }, bytes)

@[simp] theorem encode_length (message : SnapshotRefreshTickerGroup) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, MdEntryTypeTickerEntryType.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : SnapshotRefreshTickerGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SnapshotRefreshTickerGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [MdEntryTypeTickerEntryType.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end SnapshotRefreshTickerGroup

/-- Snapshot Refresh Ticker Groups -/
structure SnapshotRefreshTickerGroups where
  blockLength : BitVec 16
  snapshotRefreshTickerGroup : Bounded 1 SnapshotRefreshTickerGroup
  deriving DecidableEq, Repr

namespace SnapshotRefreshTickerGroups

def encode (message : SnapshotRefreshTickerGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.snapshotRefreshTickerGroup.val.length)
    ++ encodeMany SnapshotRefreshTickerGroup.encode message.snapshotRefreshTickerGroup.val

def decode (bytes : List UInt8) : Option (SnapshotRefreshTickerGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (snapshotRefreshTickerGroup_, bytes) ← decodeMany SnapshotRefreshTickerGroup.decode numInGroup.toNat bytes
  if fits_snapshotRefreshTickerGroup : snapshotRefreshTickerGroup_.length < 256 ^ 1 then
    pure ({ blockLength, snapshotRefreshTickerGroup := ⟨snapshotRefreshTickerGroup_, fits_snapshotRefreshTickerGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : SnapshotRefreshTickerGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SnapshotRefreshTickerGroups) : (encode message).length ≤ 7143 := by
  have bound_snapshotRefreshTickerGroup := message.snapshotRefreshTickerGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const SnapshotRefreshTickerGroup.encode 28 SnapshotRefreshTickerGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : SnapshotRefreshTickerGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeMany_bounded 1 SnapshotRefreshTickerGroup.encode SnapshotRefreshTickerGroup.decode SnapshotRefreshTickerGroup.decode_encode, Option.bind_some]
  dsimp only
  simp only [message.snapshotRefreshTickerGroup.length_lt, ↓reduceDIte]
  rfl

end SnapshotRefreshTickerGroups

/-- Md Snapshot Refresh Ticker -/
structure MdSnapshotRefreshTicker where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  financialInstrumentFullName : Alpha 35
  symbol : Alpha 20
  instrumentGuid : BitVec 64
  securityId : BitVec 32
  snapshotRefreshTickerGroups : SnapshotRefreshTickerGroups
  deriving DecidableEq, Repr

namespace MdSnapshotRefreshTicker

def encode (message : MdSnapshotRefreshTicker) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ Alpha.encode message.financialInstrumentFullName
    ++ Alpha.encode message.symbol
    ++ encodeUIntLE 8 message.instrumentGuid
    ++ encodeUIntLE 4 message.securityId
    ++ SnapshotRefreshTickerGroups.encode message.snapshotRefreshTickerGroups

def decode (bytes : List UInt8) : Option (MdSnapshotRefreshTicker × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (financialInstrumentFullName, bytes) ← Alpha.decode 35 bytes
  let (symbol, bytes) ← Alpha.decode 20 bytes
  let (instrumentGuid, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (snapshotRefreshTickerGroups, bytes) ← SnapshotRefreshTickerGroups.decode bytes
  pure ({ transactTime, matchEventIndicator, financialInstrumentFullName, symbol, instrumentGuid, securityId, snapshotRefreshTickerGroups }, bytes)

theorem encode_length_pos (message : MdSnapshotRefreshTicker) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdSnapshotRefreshTicker) : (encode message).length ≤ 7219 := by
  have bound_snapshotRefreshTickerGroups := SnapshotRefreshTickerGroups.encode_length_le message.snapshotRefreshTickerGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : MdSnapshotRefreshTicker) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [SnapshotRefreshTickerGroups.decode_encode, Option.bind_some]
  rfl

end MdSnapshotRefreshTicker

/-- Global Day Roll: 9 bytes -/
structure GlobalDayRoll where
  transactTime : BitVec 64
  securityTradingEvent : BitVec 8
  deriving DecidableEq, Repr

namespace GlobalDayRoll

def encode (message : GlobalDayRoll) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUInt 1 message.securityTradingEvent

def decode (bytes : List UInt8) : Option (GlobalDayRoll × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (securityTradingEvent, bytes) ← decodeUInt 1 bytes
  pure ({ transactTime, securityTradingEvent }, bytes)

@[simp] theorem encode_length (message : GlobalDayRoll) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : GlobalDayRoll) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GlobalDayRoll) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end GlobalDayRoll

/-- Any Payload, selected by Template Id -/
inductive Payload where
  | adminHeartbeat (message : AdminHeartbeat) -- 302
  | mdIncrementalRefreshSpectrum (message : MdIncrementalRefreshSpectrum) -- 303
  | mdIncrementalRefreshTicker (message : MdIncrementalRefreshTicker) -- 304
  | mdSnapshotRefreshSpectrum (message : MdSnapshotRefreshSpectrum) -- 305
  | mdSnapshotRefreshTicker (message : MdSnapshotRefreshTicker) -- 306
  | globalDayRoll (message : GlobalDayRoll) -- 307
  deriving DecidableEq, Repr

namespace Payload

/-- The Template Id each message is sent under -/
def tag : Payload → BitVec 16
  | .adminHeartbeat _ => 302
  | .mdIncrementalRefreshSpectrum _ => 303
  | .mdIncrementalRefreshTicker _ => 304
  | .mdSnapshotRefreshSpectrum _ => 305
  | .mdSnapshotRefreshTicker _ => 306
  | .globalDayRoll _ => 307

def encode : Payload → List UInt8
  | .adminHeartbeat message => AdminHeartbeat.encode message
  | .mdIncrementalRefreshSpectrum message => MdIncrementalRefreshSpectrum.encode message
  | .mdIncrementalRefreshTicker message => MdIncrementalRefreshTicker.encode message
  | .mdSnapshotRefreshSpectrum message => MdSnapshotRefreshSpectrum.encode message
  | .mdSnapshotRefreshTicker message => MdSnapshotRefreshTicker.encode message
  | .globalDayRoll message => GlobalDayRoll.encode message

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 302 then (AdminHeartbeat.decode bytes).map fun (message, rest) => (.adminHeartbeat message, rest)
  else if tag = 303 then (MdIncrementalRefreshSpectrum.decode bytes).map fun (message, rest) => (.mdIncrementalRefreshSpectrum message, rest)
  else if tag = 304 then (MdIncrementalRefreshTicker.decode bytes).map fun (message, rest) => (.mdIncrementalRefreshTicker message, rest)
  else if tag = 305 then (MdSnapshotRefreshSpectrum.decode bytes).map fun (message, rest) => (.mdSnapshotRefreshSpectrum message, rest)
  else if tag = 306 then (MdSnapshotRefreshTicker.decode bytes).map fun (message, rest) => (.mdSnapshotRefreshTicker message, rest)
  else if tag = 307 then (GlobalDayRoll.decode bytes).map fun (message, rest) => (.globalDayRoll message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Tcp Message -/
structure TcpMessage where
  blockLength : BitVec 16
  schemaId : BitVec 16
  version : BitVec 16
  payload : Payload
  deriving DecidableEq, Repr

namespace TcpMessage

def encodeBody (message : TcpMessage) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUIntLE 2 (Payload.tag message.payload)
    ++ encodeUIntLE 2 message.schemaId
    ++ encodeUIntLE 2 message.version
    ++ Payload.encode message.payload

def decodeBody (bytes : List UInt8) : Option (TcpMessage × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (templateId, bytes) ← decodeUIntLE 2 bytes
  let (schemaId, bytes) ← decodeUIntLE 2 bytes
  let (version, bytes) ← decodeUIntLE 2 bytes
  let (payload, bytes) ← Payload.decode templateId bytes
  pure ({ blockLength, schemaId, version, payload }, bytes)

theorem decodeBody_encodeBody (message : TcpMessage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [Payload.decode_encode, Option.bind_some]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : TcpMessage) : (encodeBody message).length + 2 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | adminHeartbeat inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, AdminHeartbeat.encode_length]
    omega
  | mdIncrementalRefreshSpectrum inner =>
    have bound_inner := MdIncrementalRefreshSpectrum.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | mdIncrementalRefreshTicker inner =>
    have bound_inner := MdIncrementalRefreshTicker.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | mdSnapshotRefreshSpectrum inner =>
    have bound_inner := MdSnapshotRefreshSpectrum.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | mdSnapshotRefreshTicker inner =>
    have bound_inner := MdSnapshotRefreshTicker.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | globalDayRoll inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, GlobalDayRoll.encode_length]
    omega

/-- Size rule: Tcp Message Size counts the bytes after it plus 2, so it is written from the body and checked on decode -/
def encode : TcpMessage → List UInt8 :=
  encodeFramedLE 2 2 encodeBody

def decode : List UInt8 → Option (TcpMessage × List UInt8) :=
  decodeFramedLE 2 2 decodeBody

@[simp] theorem decode_encode (message : TcpMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 2 encodeBody decodeBody decodeBody_encodeBody encodeBody_length_lt message rest

theorem encode_length_pos (message : TcpMessage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end TcpMessage

/-- Tcp Packet -/
structure TcpPacket where
  technicalHeader : TechnicalHeader
  tcpMessage : List TcpMessage
  deriving DecidableEq, Repr

namespace TcpPacket

def encode (message : TcpPacket) : List UInt8 :=
  TechnicalHeader.encode message.technicalHeader
    ++ encodeMany TcpMessage.encode message.tcpMessage

def decode (bytes : List UInt8) : Option TcpPacket := do
  let (technicalHeader, bytes) ← TechnicalHeader.decode bytes
  let tcpMessage ← decodeAll TcpMessage.decode bytes.length bytes
  pure { technicalHeader, tcpMessage }

theorem encode_length_pos (message : TcpPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [TechnicalHeader.encode_length, List.length_append]
  omega

theorem decode_encode (message : TcpPacket) : decode (encode message) = some message := by
  unfold decode encode
  simp only [Option.bind_eq_bind]
  rw [TechnicalHeader.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeAll_encodeMany TcpMessage.encode TcpMessage.decode TcpMessage.decode_encode TcpMessage.encode_length_pos message.tcpMessage _ (encodeMany_length_ge TcpMessage.encode TcpMessage.encode_length_pos message.tcpMessage), Option.bind_some]
  rfl

end TcpPacket

end Omi.CmeGlobexDerivedSbeV120Tcp
