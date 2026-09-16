import Omi.Wire

/-!
# CME Group Ebs Spectrum Market Data v12.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Match Event Indicator is a bit field set, proven as its 1 byte integer rather than bit by bit.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.CmeGlobexEbsspectrumSbeV120Udp

/-- Md Entry Type Spectrum Entry Type: one byte code -/
inductive MdEntryTypeSpectrumEntryType where
  | vwap -- Vwap
  | twap -- Twap
  deriving DecidableEq, Repr

namespace MdEntryTypeSpectrumEntryType

def toByte : MdEntryTypeSpectrumEntryType → UInt8
  | .vwap => 0x39
  | .twap => 0x74

def ofByte? (byte : UInt8) : Option MdEntryTypeSpectrumEntryType :=
  if byte = 0x39 then some .vwap
  else if byte = 0x74 then some .twap
  else none

theorem ofByte?_toByte (value : MdEntryTypeSpectrumEntryType) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : MdEntryTypeSpectrumEntryType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MdEntryTypeSpectrumEntryType × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : MdEntryTypeSpectrumEntryType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MdEntryTypeSpectrumEntryType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end MdEntryTypeSpectrumEntryType

/-- Md Entry Type Ticker Entry Type: one byte code -/
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

def ofByte? (byte : UInt8) : Option MdEntryTypeTickerEntryType :=
  if byte = 0x6B then some .touchHigh
  else if byte = 0x6C then some .touchLow
  else if byte = 0x6D then some .openBestBid
  else if byte = 0x6E then some .openBestOffer
  else if byte = 0x6F then some .closeBestBid
  else if byte = 0x70 then some .closeBestOffer
  else if byte = 0x71 then some .marketHigh
  else if byte = 0x72 then some .marketLow
  else if byte = 0x77 then some .marketBestOffer
  else if byte = 0x78 then some .marketBestBid
  else if byte = 0x79 then some .paid
  else if byte = 0x7A then some .given
  else none

theorem ofByte?_toByte (value : MdEntryTypeTickerEntryType) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : MdEntryTypeTickerEntryType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MdEntryTypeTickerEntryType × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : MdEntryTypeTickerEntryType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MdEntryTypeTickerEntryType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end MdEntryTypeTickerEntryType

/-- Binary Packet Header: 12 bytes -/
structure BinaryPacketHeader where
  packetSequenceNumber : BitVec 32
  sendingTime : BitVec 64
  deriving DecidableEq, Repr

namespace BinaryPacketHeader

def encode (message : BinaryPacketHeader) : List UInt8 :=
  encodeUIntLE 4 message.packetSequenceNumber
    ++ encodeUIntLE 8 message.sendingTime

def decode (bytes : List UInt8) : Option (BinaryPacketHeader × List UInt8) := do
  let (packetSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ packetSequenceNumber, sendingTime }, bytes)

@[simp] theorem encode_length (message : BinaryPacketHeader) : (encode message).length = 12 := by
  simp [encode]

theorem encode_length_pos (message : BinaryPacketHeader) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : BinaryPacketHeader) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end BinaryPacketHeader

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
  simp [decode, encode, List.append_assoc]

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
  simp [encode]

theorem encode_length_pos (message : IncrementalRefreshSpectrumGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : IncrementalRefreshSpectrumGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end IncrementalRefreshSpectrumGroup

/-- Md Incremental Refresh Spectrum -/
structure MdIncrementalRefreshSpectrum where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  blockLength : BitVec 16
  incrementalRefreshSpectrumGroup : Bounded 1 IncrementalRefreshSpectrumGroup
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshSpectrum

def encode (message : MdIncrementalRefreshSpectrum) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.incrementalRefreshSpectrumGroup.val.length)
    ++ encodeMany IncrementalRefreshSpectrumGroup.encode message.incrementalRefreshSpectrumGroup.val

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshSpectrum × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshSpectrumGroup_, bytes) ← decodeMany IncrementalRefreshSpectrumGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshSpectrumGroup : incrementalRefreshSpectrumGroup_.length < 256 then
    pure ({ transactTime, matchEventIndicator, blockLength, incrementalRefreshSpectrumGroup := ⟨incrementalRefreshSpectrumGroup_, fits_incrementalRefreshSpectrumGroup⟩ }, bytes)
  else none

@[simp] theorem decode_encode (message : MdIncrementalRefreshSpectrum) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  have fits_incrementalRefreshSpectrumGroup : message.incrementalRefreshSpectrumGroup.val.length < 256 := by simpa using message.incrementalRefreshSpectrumGroup.length_lt
  simp [decode, encode, List.append_assoc, Nat.mod_eq_of_lt fits_incrementalRefreshSpectrumGroup, fits_incrementalRefreshSpectrumGroup, decodeMany_encodeMany IncrementalRefreshSpectrumGroup.encode IncrementalRefreshSpectrumGroup.decode IncrementalRefreshSpectrumGroup.decode_encode]

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
  simp [encode]

theorem encode_length_pos (message : IncrementalRefreshTickerGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : IncrementalRefreshTickerGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end IncrementalRefreshTickerGroup

/-- Md Incremental Refresh Ticker -/
structure MdIncrementalRefreshTicker where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  blockLength : BitVec 16
  incrementalRefreshTickerGroup : Bounded 1 IncrementalRefreshTickerGroup
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshTicker

def encode (message : MdIncrementalRefreshTicker) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.incrementalRefreshTickerGroup.val.length)
    ++ encodeMany IncrementalRefreshTickerGroup.encode message.incrementalRefreshTickerGroup.val

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshTicker × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshTickerGroup_, bytes) ← decodeMany IncrementalRefreshTickerGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshTickerGroup : incrementalRefreshTickerGroup_.length < 256 then
    pure ({ transactTime, matchEventIndicator, blockLength, incrementalRefreshTickerGroup := ⟨incrementalRefreshTickerGroup_, fits_incrementalRefreshTickerGroup⟩ }, bytes)
  else none

@[simp] theorem decode_encode (message : MdIncrementalRefreshTicker) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  have fits_incrementalRefreshTickerGroup : message.incrementalRefreshTickerGroup.val.length < 256 := by simpa using message.incrementalRefreshTickerGroup.length_lt
  simp [decode, encode, List.append_assoc, Nat.mod_eq_of_lt fits_incrementalRefreshTickerGroup, fits_incrementalRefreshTickerGroup, decodeMany_encodeMany IncrementalRefreshTickerGroup.encode IncrementalRefreshTickerGroup.decode IncrementalRefreshTickerGroup.decode_encode]

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
  simp [encode]

theorem encode_length_pos (message : SnapshotRefreshSpectrumGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : SnapshotRefreshSpectrumGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end SnapshotRefreshSpectrumGroup

/-- Md Snapshot Refresh Spectrum -/
structure MdSnapshotRefreshSpectrum where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  financialInstrumentFullName : Alpha 35
  symbol : Alpha 20
  instrumentGuid : BitVec 64
  securityId : BitVec 32
  blockLength : BitVec 16
  snapshotRefreshSpectrumGroup : Bounded 1 SnapshotRefreshSpectrumGroup
  deriving DecidableEq, Repr

namespace MdSnapshotRefreshSpectrum

def encode (message : MdSnapshotRefreshSpectrum) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ Alpha.encode message.financialInstrumentFullName
    ++ Alpha.encode message.symbol
    ++ encodeUIntLE 8 message.instrumentGuid
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.snapshotRefreshSpectrumGroup.val.length)
    ++ encodeMany SnapshotRefreshSpectrumGroup.encode message.snapshotRefreshSpectrumGroup.val

def decode (bytes : List UInt8) : Option (MdSnapshotRefreshSpectrum × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (financialInstrumentFullName, bytes) ← Alpha.decode 35 bytes
  let (symbol, bytes) ← Alpha.decode 20 bytes
  let (instrumentGuid, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (snapshotRefreshSpectrumGroup_, bytes) ← decodeMany SnapshotRefreshSpectrumGroup.decode numInGroup.toNat bytes
  if fits_snapshotRefreshSpectrumGroup : snapshotRefreshSpectrumGroup_.length < 256 then
    pure ({ transactTime, matchEventIndicator, financialInstrumentFullName, symbol, instrumentGuid, securityId, blockLength, snapshotRefreshSpectrumGroup := ⟨snapshotRefreshSpectrumGroup_, fits_snapshotRefreshSpectrumGroup⟩ }, bytes)
  else none

@[simp] theorem decode_encode (message : MdSnapshotRefreshSpectrum) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  have fits_snapshotRefreshSpectrumGroup : message.snapshotRefreshSpectrumGroup.val.length < 256 := by simpa using message.snapshotRefreshSpectrumGroup.length_lt
  simp [decode, encode, List.append_assoc, Nat.mod_eq_of_lt fits_snapshotRefreshSpectrumGroup, fits_snapshotRefreshSpectrumGroup, decodeMany_encodeMany SnapshotRefreshSpectrumGroup.encode SnapshotRefreshSpectrumGroup.decode SnapshotRefreshSpectrumGroup.decode_encode]

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
  simp [encode]

theorem encode_length_pos (message : SnapshotRefreshTickerGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : SnapshotRefreshTickerGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end SnapshotRefreshTickerGroup

/-- Md Snapshot Refresh Ticker -/
structure MdSnapshotRefreshTicker where
  transactTime : BitVec 64
  matchEventIndicator : BitVec 8
  financialInstrumentFullName : Alpha 35
  symbol : Alpha 20
  instrumentGuid : BitVec 64
  securityId : BitVec 32
  blockLength : BitVec 16
  snapshotRefreshTickerGroup : Bounded 1 SnapshotRefreshTickerGroup
  deriving DecidableEq, Repr

namespace MdSnapshotRefreshTicker

def encode (message : MdSnapshotRefreshTicker) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 1 message.matchEventIndicator
    ++ Alpha.encode message.financialInstrumentFullName
    ++ Alpha.encode message.symbol
    ++ encodeUIntLE 8 message.instrumentGuid
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.snapshotRefreshTickerGroup.val.length)
    ++ encodeMany SnapshotRefreshTickerGroup.encode message.snapshotRefreshTickerGroup.val

def decode (bytes : List UInt8) : Option (MdSnapshotRefreshTicker × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (matchEventIndicator, bytes) ← decodeUIntLE 1 bytes
  let (financialInstrumentFullName, bytes) ← Alpha.decode 35 bytes
  let (symbol, bytes) ← Alpha.decode 20 bytes
  let (instrumentGuid, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (snapshotRefreshTickerGroup_, bytes) ← decodeMany SnapshotRefreshTickerGroup.decode numInGroup.toNat bytes
  if fits_snapshotRefreshTickerGroup : snapshotRefreshTickerGroup_.length < 256 then
    pure ({ transactTime, matchEventIndicator, financialInstrumentFullName, symbol, instrumentGuid, securityId, blockLength, snapshotRefreshTickerGroup := ⟨snapshotRefreshTickerGroup_, fits_snapshotRefreshTickerGroup⟩ }, bytes)
  else none

@[simp] theorem decode_encode (message : MdSnapshotRefreshTicker) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  have fits_snapshotRefreshTickerGroup : message.snapshotRefreshTickerGroup.val.length < 256 := by simpa using message.snapshotRefreshTickerGroup.length_lt
  simp [decode, encode, List.append_assoc, Nat.mod_eq_of_lt fits_snapshotRefreshTickerGroup, fits_snapshotRefreshTickerGroup, decodeMany_encodeMany SnapshotRefreshTickerGroup.encode SnapshotRefreshTickerGroup.decode SnapshotRefreshTickerGroup.decode_encode]

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
  simp [encode]

theorem encode_length_pos (message : GlobalDayRoll) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : GlobalDayRoll) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

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

/-- Message -/
structure Message where
  blockLength : BitVec 16
  schemaId : BitVec 16
  version : BitVec 16
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUIntLE 2 (Payload.tag message.payload)
    ++ encodeUIntLE 2 message.schemaId
    ++ encodeUIntLE 2 message.version
    ++ Payload.encode message.payload

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (templateId, bytes) ← decodeUIntLE 2 bytes
  let (schemaId, bytes) ← decodeUIntLE 2 bytes
  let (version, bytes) ← decodeUIntLE 2 bytes
  let (payload, bytes) ← Payload.decode templateId bytes
  pure ({ blockLength, schemaId, version, payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  simp [decodeBody, encodeBody, List.append_assoc]

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 2 < 65536 := by
  cases h : message.payload with
  | adminHeartbeat inner =>
    simp [encodeBody, h, Payload.encode, AdminHeartbeat.encode]
  | mdIncrementalRefreshSpectrum inner =>
    have bound_mdIncrementalRefreshSpectrum_incrementalRefreshSpectrumGroup := inner.incrementalRefreshSpectrumGroup.length_lt
    simp [encodeBody, h, Payload.encode, MdIncrementalRefreshSpectrum.encode, encodeMany_length_const IncrementalRefreshSpectrumGroup.encode 92 IncrementalRefreshSpectrumGroup.encode_length]
    omega
  | mdIncrementalRefreshTicker inner =>
    have bound_mdIncrementalRefreshTicker_incrementalRefreshTickerGroup := inner.incrementalRefreshTickerGroup.length_lt
    simp [encodeBody, h, Payload.encode, MdIncrementalRefreshTicker.encode, encodeMany_length_const IncrementalRefreshTickerGroup.encode 95 IncrementalRefreshTickerGroup.encode_length]
    omega
  | mdSnapshotRefreshSpectrum inner =>
    have bound_mdSnapshotRefreshSpectrum_snapshotRefreshSpectrumGroup := inner.snapshotRefreshSpectrumGroup.length_lt
    simp [encodeBody, h, Payload.encode, MdSnapshotRefreshSpectrum.encode, encodeMany_length_const SnapshotRefreshSpectrumGroup.encode 25 SnapshotRefreshSpectrumGroup.encode_length]
    omega
  | mdSnapshotRefreshTicker inner =>
    have bound_mdSnapshotRefreshTicker_snapshotRefreshTickerGroup := inner.snapshotRefreshTickerGroup.length_lt
    simp [encodeBody, h, Payload.encode, MdSnapshotRefreshTicker.encode, encodeMany_length_const SnapshotRefreshTickerGroup.encode 28 SnapshotRefreshTickerGroup.encode_length]
    omega
  | globalDayRoll inner =>
    simp [encodeBody, h, Payload.encode, GlobalDayRoll.encode]

/-- Size rule: Message Size counts the bytes after it plus 2, so it is written from the body -/
def encode : Message → List UInt8 :=
  encodeFramedLE 2 2 encodeBody

def decode : List UInt8 → Option (Message × List UInt8) :=
  decodeFramedLE 2 2 decodeBody

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 2 encodeBody decodeBody decodeBody_encodeBody encodeBody_length_lt message rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end Message

/-- Udp Packet -/
structure UdpPacket where
  binaryPacketHeader : BinaryPacketHeader
  message : List Message
  deriving DecidableEq, Repr

namespace UdpPacket

def encode (message : UdpPacket) : List UInt8 :=
  BinaryPacketHeader.encode message.binaryPacketHeader
    ++ encodeMany Message.encode message.message

def decode (bytes : List UInt8) : Option UdpPacket := do
  let (binaryPacketHeader, bytes) ← BinaryPacketHeader.decode bytes
  let message ← decodeAll Message.decode bytes.length bytes
  pure { binaryPacketHeader, message }

theorem decode_encode (message : UdpPacket) : decode (encode message) = some message := by
  simp [decode, encode, List.append_assoc, decodeAll_encodeMany Message.encode Message.decode Message.decode_encode Message.encode_length_pos message.message _ (encodeMany_length_ge Message.encode Message.encode_length_pos message.message)]

end UdpPacket

end Omi.CmeGlobexEbsspectrumSbeV120Udp
