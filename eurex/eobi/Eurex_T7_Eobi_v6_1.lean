import Omi.Wire

/-!
# Eurex Exchange Enhanced Order Book Interface v6.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.EurexT7EobiFbeV61

/-- Eobi Header: 8 bytes -/
structure EobiHeader where
  bodyLen : BitVec 16
  templateId : BitVec 16
  msgSeqNum : BitVec 32
  deriving DecidableEq, Repr

namespace EobiHeader

def encode (message : EobiHeader) : List UInt8 :=
  encodeUIntLE 2 message.bodyLen
    ++ encodeUIntLE 2 message.templateId
    ++ encodeUIntLE 4 message.msgSeqNum

def decode (bytes : List UInt8) : Option (EobiHeader × List UInt8) := do
  let (bodyLen, bytes) ← decodeUIntLE 2 bytes
  let (templateId, bytes) ← decodeUIntLE 2 bytes
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  pure ({ bodyLen, templateId, msgSeqNum }, bytes)

@[simp] theorem encode_length (message : EobiHeader) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : EobiHeader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EobiHeader) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end EobiHeader

/-- Packet Header: 32 bytes -/
structure PacketHeader where
  eobiHeader : EobiHeader
  applSeqNum : BitVec 64
  marketSegmentId : BitVec 32
  partitionId : BitVec 8
  completionIndicator : BitVec 8
  applSeqResetIndicator : BitVec 8
  pad1 : Alpha 1
  transactTime : BitVec 64
  deriving DecidableEq, Repr

namespace PacketHeader

def encode (message : PacketHeader) : List UInt8 :=
  EobiHeader.encode message.eobiHeader
    ++ encodeUIntLE 8 message.applSeqNum
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUInt 1 message.partitionId
    ++ encodeUInt 1 message.completionIndicator
    ++ encodeUInt 1 message.applSeqResetIndicator
    ++ Alpha.encode message.pad1
    ++ encodeUIntLE 8 message.transactTime

def decode (bytes : List UInt8) : Option (PacketHeader × List UInt8) := do
  let (eobiHeader, bytes) ← EobiHeader.decode bytes
  let (applSeqNum, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (partitionId, bytes) ← decodeUInt 1 bytes
  let (completionIndicator, bytes) ← decodeUInt 1 bytes
  let (applSeqResetIndicator, bytes) ← decodeUInt 1 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ eobiHeader, applSeqNum, marketSegmentId, partitionId, completionIndicator, applSeqResetIndicator, pad1, transactTime }, bytes)

@[simp] theorem encode_length (message : PacketHeader) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, EobiHeader.encode_length, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : PacketHeader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PacketHeader) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [EobiHeader.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end PacketHeader

/-- Instrmt Leg Grp Comp: 24 bytes -/
structure InstrmtLegGrpComp where
  legSymbol : BitVec 32
  pad4 : Alpha 4
  legSecurityId : BitVec 64
  legRatioQty : BitVec 32
  legSide : BitVec 8
  pad3 : Alpha 3
  deriving DecidableEq, Repr

namespace InstrmtLegGrpComp

def encode (message : InstrmtLegGrpComp) : List UInt8 :=
  encodeUIntLE 4 message.legSymbol
    ++ Alpha.encode message.pad4
    ++ encodeUIntLE 8 message.legSecurityId
    ++ encodeUIntLE 4 message.legRatioQty
    ++ encodeUInt 1 message.legSide
    ++ Alpha.encode message.pad3

def decode (bytes : List UInt8) : Option (InstrmtLegGrpComp × List UInt8) := do
  let (legSymbol, bytes) ← decodeUIntLE 4 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  let (legSecurityId, bytes) ← decodeUIntLE 8 bytes
  let (legRatioQty, bytes) ← decodeUIntLE 4 bytes
  let (legSide, bytes) ← decodeUInt 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  pure ({ legSymbol, pad4, legSecurityId, legRatioQty, legSide, pad3 }, bytes)

@[simp] theorem encode_length (message : InstrmtLegGrpComp) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : InstrmtLegGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrmtLegGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end InstrmtLegGrpComp

/-- Add Complex Instrument -/
structure AddComplexInstrument where
  securityId : BitVec 64
  transactTime : BitVec 64
  securitySubType : BitVec 32
  productComplex : BitVec 8
  impliedMarketIndicator : BitVec 8
  pad1 : Alpha 1
  instrmtLegGrpComp : Bounded 1 InstrmtLegGrpComp
  deriving DecidableEq, Repr

namespace AddComplexInstrument

def encode (message : AddComplexInstrument) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 4 message.securitySubType
    ++ encodeUInt 1 message.productComplex
    ++ encodeUInt 1 message.impliedMarketIndicator
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.instrmtLegGrpComp.val.length)
    ++ Alpha.encode message.pad1
    ++ encodeMany InstrmtLegGrpComp.encode message.instrmtLegGrpComp.val

def decode (bytes : List UInt8) : Option (AddComplexInstrument × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (securitySubType, bytes) ← decodeUIntLE 4 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (impliedMarketIndicator, bytes) ← decodeUInt 1 bytes
  let (noLegs, bytes) ← decodeUInt 1 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  let (instrmtLegGrpComp_, bytes) ← decodeMany InstrmtLegGrpComp.decode noLegs.toNat bytes
  if fits_instrmtLegGrpComp : instrmtLegGrpComp_.length < 256 ^ 1 then
    pure ({ securityId, transactTime, securitySubType, productComplex, impliedMarketIndicator, pad1, instrmtLegGrpComp := ⟨instrmtLegGrpComp_, fits_instrmtLegGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : AddComplexInstrument) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : AddComplexInstrument) : (encode message).length ≤ 6144 := by
  have bound_instrmtLegGrpComp := message.instrmtLegGrpComp.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, encodeMany_length_const InstrmtLegGrpComp.encode 24 InstrmtLegGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : AddComplexInstrument) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 InstrmtLegGrpComp.encode InstrmtLegGrpComp.decode InstrmtLegGrpComp.decode_encode]
  simp only [Option.bind_some]
  simp only [message.instrmtLegGrpComp.length_lt, ↓reduceDIte]
  rfl

end AddComplexInstrument

/-- Auction Bbo: 48 bytes -/
structure AuctionBbo where
  transactTime : BitVec 64
  securityId : BitVec 64
  bidPx : BitVec 64
  offerPx : BitVec 64
  bidSize : BitVec 32
  offerSize : BitVec 32
  potentialSecurityTradingEvent : BitVec 8
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace AuctionBbo

def encode (message : AuctionBbo) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.bidPx
    ++ encodeUIntLE 8 message.offerPx
    ++ encodeUIntLE 4 message.bidSize
    ++ encodeUIntLE 4 message.offerSize
    ++ encodeUInt 1 message.potentialSecurityTradingEvent
    ++ Alpha.encode message.pad7

def decode (bytes : List UInt8) : Option (AuctionBbo × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (bidPx, bytes) ← decodeUIntLE 8 bytes
  let (offerPx, bytes) ← decodeUIntLE 8 bytes
  let (bidSize, bytes) ← decodeUIntLE 4 bytes
  let (offerSize, bytes) ← decodeUIntLE 4 bytes
  let (potentialSecurityTradingEvent, bytes) ← decodeUInt 1 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ transactTime, securityId, bidPx, offerPx, bidSize, offerSize, potentialSecurityTradingEvent, pad7 }, bytes)

@[simp] theorem encode_length (message : AuctionBbo) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : AuctionBbo) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AuctionBbo) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end AuctionBbo

/-- Auction Clearing Price: 40 bytes -/
structure AuctionClearingPrice where
  transactTime : BitVec 64
  securityId : BitVec 64
  lastPx : BitVec 64
  lastQty : BitVec 32
  imbalanceQty : BitVec 32
  securityTradingStatus : BitVec 8
  potentialSecurityTradingEvent : BitVec 8
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace AuctionClearingPrice

def encode (message : AuctionClearingPrice) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.lastPx
    ++ encodeUIntLE 4 message.lastQty
    ++ encodeUIntLE 4 message.imbalanceQty
    ++ encodeUInt 1 message.securityTradingStatus
    ++ encodeUInt 1 message.potentialSecurityTradingEvent
    ++ Alpha.encode message.pad6

def decode (bytes : List UInt8) : Option (AuctionClearingPrice × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (imbalanceQty, bytes) ← decodeUIntLE 4 bytes
  let (securityTradingStatus, bytes) ← decodeUInt 1 bytes
  let (potentialSecurityTradingEvent, bytes) ← decodeUInt 1 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ transactTime, securityId, lastPx, lastQty, imbalanceQty, securityTradingStatus, potentialSecurityTradingEvent, pad6 }, bytes)

@[simp] theorem encode_length (message : AuctionClearingPrice) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : AuctionClearingPrice) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AuctionClearingPrice) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end AuctionClearingPrice

/-- Cross Request: 24 bytes -/
structure CrossRequest where
  securityId : BitVec 64
  lastQty : BitVec 32
  pad4 : Alpha 4
  transactTime : BitVec 64
  deriving DecidableEq, Repr

namespace CrossRequest

def encode (message : CrossRequest) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 4 message.lastQty
    ++ Alpha.encode message.pad4
    ++ encodeUIntLE 8 message.transactTime

def decode (bytes : List UInt8) : Option (CrossRequest × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityId, lastQty, pad4, transactTime }, bytes)

@[simp] theorem encode_length (message : CrossRequest) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : CrossRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CrossRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end CrossRequest

/-- Execution Summary: 56 bytes -/
structure ExecutionSummary where
  securityId : BitVec 64
  aggressorTime : BitVec 64
  requestTime : BitVec 64
  execId : BitVec 64
  lastQty : BitVec 32
  aggressorSide : BitVec 8
  tradeCondition : BitVec 8
  pad2 : Alpha 2
  lastPx : BitVec 64
  restingHiddenQty : BitVec 32
  restingCxlQty : BitVec 32
  deriving DecidableEq, Repr

namespace ExecutionSummary

def encode (message : ExecutionSummary) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.aggressorTime
    ++ encodeUIntLE 8 message.requestTime
    ++ encodeUIntLE 8 message.execId
    ++ encodeUIntLE 4 message.lastQty
    ++ encodeUInt 1 message.aggressorSide
    ++ encodeUInt 1 message.tradeCondition
    ++ Alpha.encode message.pad2
    ++ encodeUIntLE 8 message.lastPx
    ++ encodeUIntLE 4 message.restingHiddenQty
    ++ encodeUIntLE 4 message.restingCxlQty

def decode (bytes : List UInt8) : Option (ExecutionSummary × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (aggressorTime, bytes) ← decodeUIntLE 8 bytes
  let (requestTime, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (aggressorSide, bytes) ← decodeUInt 1 bytes
  let (tradeCondition, bytes) ← decodeUInt 1 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (restingHiddenQty, bytes) ← decodeUIntLE 4 bytes
  let (restingCxlQty, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityId, aggressorTime, requestTime, execId, lastQty, aggressorSide, tradeCondition, pad2, lastPx, restingHiddenQty, restingCxlQty }, bytes)

@[simp] theorem encode_length (message : ExecutionSummary) : (encode message).length = 56 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : ExecutionSummary) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutionSummary) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end ExecutionSummary

/-- Full Order Execution: 44 bytes -/
structure FullOrderExecution where
  side : BitVec 8
  ordType : BitVec 8
  algorithmicTradeIndicator : BitVec 8
  pad1 : Alpha 1
  price : BitVec 64
  trdRegTsTimePriority : BitVec 64
  securityId : BitVec 64
  trdMatchId : BitVec 32
  lastQty : BitVec 32
  lastPx : BitVec 64
  deriving DecidableEq, Repr

namespace FullOrderExecution

def encode (message : FullOrderExecution) : List UInt8 :=
  encodeUInt 1 message.side
    ++ encodeUInt 1 message.ordType
    ++ encodeUInt 1 message.algorithmicTradeIndicator
    ++ Alpha.encode message.pad1
    ++ encodeUIntLE 8 message.price
    ++ encodeUIntLE 8 message.trdRegTsTimePriority
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 4 message.trdMatchId
    ++ encodeUIntLE 4 message.lastQty
    ++ encodeUIntLE 8 message.lastPx

def decode (bytes : List UInt8) : Option (FullOrderExecution × List UInt8) := do
  let (side, bytes) ← decodeUInt 1 bytes
  let (ordType, bytes) ← decodeUInt 1 bytes
  let (algorithmicTradeIndicator, bytes) ← decodeUInt 1 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsTimePriority, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (trdMatchId, bytes) ← decodeUIntLE 4 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  pure ({ side, ordType, algorithmicTradeIndicator, pad1, price, trdRegTsTimePriority, securityId, trdMatchId, lastQty, lastPx }, bytes)

@[simp] theorem encode_length (message : FullOrderExecution) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : FullOrderExecution) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FullOrderExecution) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end FullOrderExecution

/-- Heartbeat: 8 bytes -/
structure Heartbeat where
  lastMsgSeqNumProcessed : BitVec 32
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace Heartbeat

def encode (message : Heartbeat) : List UInt8 :=
  encodeUIntLE 4 message.lastMsgSeqNumProcessed
    ++ Alpha.encode message.pad4

def decode (bytes : List UInt8) : Option (Heartbeat × List UInt8) := do
  let (lastMsgSeqNumProcessed, bytes) ← decodeUIntLE 4 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ lastMsgSeqNumProcessed, pad4 }, bytes)

@[simp] theorem encode_length (message : Heartbeat) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : Heartbeat) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Heartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end Heartbeat

/-- Instrument State Change: 24 bytes -/
structure InstrumentStateChange where
  securityId : BitVec 64
  securityStatus : BitVec 8
  securityTradingStatus : BitVec 8
  marketCondition : BitVec 8
  fastMarketIndicator : BitVec 8
  securityTradingEvent : BitVec 8
  pad3 : Alpha 3
  transactTime : BitVec 64
  deriving DecidableEq, Repr

namespace InstrumentStateChange

def encode (message : InstrumentStateChange) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ encodeUInt 1 message.securityStatus
    ++ encodeUInt 1 message.securityTradingStatus
    ++ encodeUInt 1 message.marketCondition
    ++ encodeUInt 1 message.fastMarketIndicator
    ++ encodeUInt 1 message.securityTradingEvent
    ++ Alpha.encode message.pad3
    ++ encodeUIntLE 8 message.transactTime

def decode (bytes : List UInt8) : Option (InstrumentStateChange × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (securityStatus, bytes) ← decodeUInt 1 bytes
  let (securityTradingStatus, bytes) ← decodeUInt 1 bytes
  let (marketCondition, bytes) ← decodeUInt 1 bytes
  let (fastMarketIndicator, bytes) ← decodeUInt 1 bytes
  let (securityTradingEvent, bytes) ← decodeUInt 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityId, securityStatus, securityTradingStatus, marketCondition, fastMarketIndicator, securityTradingEvent, pad3, transactTime }, bytes)

@[simp] theorem encode_length (message : InstrumentStateChange) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : InstrumentStateChange) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentStateChange) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end InstrumentStateChange

/-- Md Instrument Entry Grp Comp: 16 bytes -/
structure MdInstrumentEntryGrpComp where
  mdEntryPx : BitVec 64
  mdEntrySize : BitVec 32
  mdEntryType : BitVec 8
  tradeCondition : BitVec 8
  pad2 : Alpha 2
  deriving DecidableEq, Repr

namespace MdInstrumentEntryGrpComp

def encode (message : MdInstrumentEntryGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.mdEntryPx
    ++ encodeUIntLE 4 message.mdEntrySize
    ++ encodeUInt 1 message.mdEntryType
    ++ encodeUInt 1 message.tradeCondition
    ++ Alpha.encode message.pad2

def decode (bytes : List UInt8) : Option (MdInstrumentEntryGrpComp × List UInt8) := do
  let (mdEntryPx, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySize, bytes) ← decodeUIntLE 4 bytes
  let (mdEntryType, bytes) ← decodeUInt 1 bytes
  let (tradeCondition, bytes) ← decodeUInt 1 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  pure ({ mdEntryPx, mdEntrySize, mdEntryType, tradeCondition, pad2 }, bytes)

@[simp] theorem encode_length (message : MdInstrumentEntryGrpComp) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : MdInstrumentEntryGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MdInstrumentEntryGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end MdInstrumentEntryGrpComp

/-- Instrument Summary -/
structure InstrumentSummary where
  securityId : BitVec 64
  lastUpdateTime : BitVec 64
  trdRegTsExecutionTime : BitVec 64
  totNoOrders : BitVec 16
  securityStatus : BitVec 8
  securityTradingStatus : BitVec 8
  marketCondition : BitVec 8
  fastMarketIndicator : BitVec 8
  securityTradingEvent : BitVec 8
  mdInstrumentEntryGrpComp : Bounded 1 MdInstrumentEntryGrpComp
  deriving DecidableEq, Repr

namespace InstrumentSummary

def encode (message : InstrumentSummary) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.lastUpdateTime
    ++ encodeUIntLE 8 message.trdRegTsExecutionTime
    ++ encodeUIntLE 2 message.totNoOrders
    ++ encodeUInt 1 message.securityStatus
    ++ encodeUInt 1 message.securityTradingStatus
    ++ encodeUInt 1 message.marketCondition
    ++ encodeUInt 1 message.fastMarketIndicator
    ++ encodeUInt 1 message.securityTradingEvent
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.mdInstrumentEntryGrpComp.val.length)
    ++ encodeMany MdInstrumentEntryGrpComp.encode message.mdInstrumentEntryGrpComp.val

def decode (bytes : List UInt8) : Option (InstrumentSummary × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (lastUpdateTime, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsExecutionTime, bytes) ← decodeUIntLE 8 bytes
  let (totNoOrders, bytes) ← decodeUIntLE 2 bytes
  let (securityStatus, bytes) ← decodeUInt 1 bytes
  let (securityTradingStatus, bytes) ← decodeUInt 1 bytes
  let (marketCondition, bytes) ← decodeUInt 1 bytes
  let (fastMarketIndicator, bytes) ← decodeUInt 1 bytes
  let (securityTradingEvent, bytes) ← decodeUInt 1 bytes
  let (noMdEntries, bytes) ← decodeUInt 1 bytes
  let (mdInstrumentEntryGrpComp_, bytes) ← decodeMany MdInstrumentEntryGrpComp.decode noMdEntries.toNat bytes
  if fits_mdInstrumentEntryGrpComp : mdInstrumentEntryGrpComp_.length < 256 ^ 1 then
    pure ({ securityId, lastUpdateTime, trdRegTsExecutionTime, totNoOrders, securityStatus, securityTradingStatus, marketCondition, fastMarketIndicator, securityTradingEvent, mdInstrumentEntryGrpComp := ⟨mdInstrumentEntryGrpComp_, fits_mdInstrumentEntryGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : InstrumentSummary) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : InstrumentSummary) : (encode message).length ≤ 4112 := by
  have bound_mdInstrumentEntryGrpComp := message.mdInstrumentEntryGrpComp.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const MdInstrumentEntryGrpComp.encode 16 MdInstrumentEntryGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : InstrumentSummary) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 MdInstrumentEntryGrpComp.encode MdInstrumentEntryGrpComp.decode MdInstrumentEntryGrpComp.decode_encode]
  simp only [Option.bind_some]
  simp only [message.mdInstrumentEntryGrpComp.length_lt, ↓reduceDIte]
  rfl

end InstrumentSummary

/-- Order Details Comp: 24 bytes -/
structure OrderDetailsComp where
  trdRegTsTimePriority : BitVec 64
  displayQty : BitVec 32
  side : BitVec 8
  ordType : BitVec 8
  pad2 : Alpha 2
  price : BitVec 64
  deriving DecidableEq, Repr

namespace OrderDetailsComp

def encode (message : OrderDetailsComp) : List UInt8 :=
  encodeUIntLE 8 message.trdRegTsTimePriority
    ++ encodeUIntLE 4 message.displayQty
    ++ encodeUInt 1 message.side
    ++ encodeUInt 1 message.ordType
    ++ Alpha.encode message.pad2
    ++ encodeUIntLE 8 message.price

def decode (bytes : List UInt8) : Option (OrderDetailsComp × List UInt8) := do
  let (trdRegTsTimePriority, bytes) ← decodeUIntLE 8 bytes
  let (displayQty, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (ordType, bytes) ← decodeUInt 1 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  pure ({ trdRegTsTimePriority, displayQty, side, ordType, pad2, price }, bytes)

@[simp] theorem encode_length (message : OrderDetailsComp) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderDetailsComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderDetailsComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end OrderDetailsComp

/-- Order Add: 40 bytes -/
structure OrderAdd where
  trdRegTsTimeIn : BitVec 64
  securityId : BitVec 64
  orderDetailsComp : OrderDetailsComp
  deriving DecidableEq, Repr

namespace OrderAdd

def encode (message : OrderAdd) : List UInt8 :=
  encodeUIntLE 8 message.trdRegTsTimeIn
    ++ encodeUIntLE 8 message.securityId
    ++ OrderDetailsComp.encode message.orderDetailsComp

def decode (bytes : List UInt8) : Option (OrderAdd × List UInt8) := do
  let (trdRegTsTimeIn, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (orderDetailsComp, bytes) ← OrderDetailsComp.decode bytes
  pure ({ trdRegTsTimeIn, securityId, orderDetailsComp }, bytes)

@[simp] theorem encode_length (message : OrderAdd) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, OrderDetailsComp.encode_length]

theorem encode_length_pos (message : OrderAdd) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderAdd) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [OrderDetailsComp.decode_encode, Option.bind_some]
  rfl

end OrderAdd

/-- Order Delete: 48 bytes -/
structure OrderDelete where
  trdRegTsTimeIn : BitVec 64
  transactTime : BitVec 64
  securityId : BitVec 64
  orderDetailsComp : OrderDetailsComp
  deriving DecidableEq, Repr

namespace OrderDelete

def encode (message : OrderDelete) : List UInt8 :=
  encodeUIntLE 8 message.trdRegTsTimeIn
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.securityId
    ++ OrderDetailsComp.encode message.orderDetailsComp

def decode (bytes : List UInt8) : Option (OrderDelete × List UInt8) := do
  let (trdRegTsTimeIn, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (orderDetailsComp, bytes) ← OrderDetailsComp.decode bytes
  pure ({ trdRegTsTimeIn, transactTime, securityId, orderDetailsComp }, bytes)

@[simp] theorem encode_length (message : OrderDelete) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, OrderDetailsComp.encode_length]

theorem encode_length_pos (message : OrderDelete) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderDelete) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [OrderDetailsComp.decode_encode, Option.bind_some]
  rfl

end OrderDelete

/-- Order Mass Delete: 16 bytes -/
structure OrderMassDelete where
  securityId : BitVec 64
  transactTime : BitVec 64
  deriving DecidableEq, Repr

namespace OrderMassDelete

def encode (message : OrderMassDelete) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.transactTime

def decode (bytes : List UInt8) : Option (OrderMassDelete × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityId, transactTime }, bytes)

@[simp] theorem encode_length (message : OrderMassDelete) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderMassDelete) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderMassDelete) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end OrderMassDelete

/-- Order Modify: 64 bytes -/
structure OrderModify where
  trdRegTsTimeIn : BitVec 64
  trdRegTsPrevTimePriority : BitVec 64
  prevPrice : BitVec 64
  prevDisplayQty : BitVec 32
  pad4 : Alpha 4
  securityId : BitVec 64
  orderDetailsComp : OrderDetailsComp
  deriving DecidableEq, Repr

namespace OrderModify

def encode (message : OrderModify) : List UInt8 :=
  encodeUIntLE 8 message.trdRegTsTimeIn
    ++ encodeUIntLE 8 message.trdRegTsPrevTimePriority
    ++ encodeUIntLE 8 message.prevPrice
    ++ encodeUIntLE 4 message.prevDisplayQty
    ++ Alpha.encode message.pad4
    ++ encodeUIntLE 8 message.securityId
    ++ OrderDetailsComp.encode message.orderDetailsComp

def decode (bytes : List UInt8) : Option (OrderModify × List UInt8) := do
  let (trdRegTsTimeIn, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsPrevTimePriority, bytes) ← decodeUIntLE 8 bytes
  let (prevPrice, bytes) ← decodeUIntLE 8 bytes
  let (prevDisplayQty, bytes) ← decodeUIntLE 4 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (orderDetailsComp, bytes) ← OrderDetailsComp.decode bytes
  pure ({ trdRegTsTimeIn, trdRegTsPrevTimePriority, prevPrice, prevDisplayQty, pad4, securityId, orderDetailsComp }, bytes)

@[simp] theorem encode_length (message : OrderModify) : (encode message).length = 64 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, OrderDetailsComp.encode_length]

theorem encode_length_pos (message : OrderModify) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderModify) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [OrderDetailsComp.decode_encode, Option.bind_some]
  rfl

end OrderModify

/-- Order Modify Same Prio: 56 bytes -/
structure OrderModifySamePrio where
  trdRegTsTimeIn : BitVec 64
  transactTime : BitVec 64
  prevDisplayQty : BitVec 32
  pad4 : Alpha 4
  securityId : BitVec 64
  orderDetailsComp : OrderDetailsComp
  deriving DecidableEq, Repr

namespace OrderModifySamePrio

def encode (message : OrderModifySamePrio) : List UInt8 :=
  encodeUIntLE 8 message.trdRegTsTimeIn
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 4 message.prevDisplayQty
    ++ Alpha.encode message.pad4
    ++ encodeUIntLE 8 message.securityId
    ++ OrderDetailsComp.encode message.orderDetailsComp

def decode (bytes : List UInt8) : Option (OrderModifySamePrio × List UInt8) := do
  let (trdRegTsTimeIn, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (prevDisplayQty, bytes) ← decodeUIntLE 4 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (orderDetailsComp, bytes) ← OrderDetailsComp.decode bytes
  pure ({ trdRegTsTimeIn, transactTime, prevDisplayQty, pad4, securityId, orderDetailsComp }, bytes)

@[simp] theorem encode_length (message : OrderModifySamePrio) : (encode message).length = 56 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, OrderDetailsComp.encode_length]

theorem encode_length_pos (message : OrderModifySamePrio) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderModifySamePrio) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [OrderDetailsComp.decode_encode, Option.bind_some]
  rfl

end OrderModifySamePrio

/-- Partial Order Execution: 44 bytes -/
structure PartialOrderExecution where
  side : BitVec 8
  ordType : BitVec 8
  algorithmicTradeIndicator : BitVec 8
  pad1 : Alpha 1
  price : BitVec 64
  trdRegTsTimePriority : BitVec 64
  securityId : BitVec 64
  trdMatchId : BitVec 32
  lastQty : BitVec 32
  lastPx : BitVec 64
  deriving DecidableEq, Repr

namespace PartialOrderExecution

def encode (message : PartialOrderExecution) : List UInt8 :=
  encodeUInt 1 message.side
    ++ encodeUInt 1 message.ordType
    ++ encodeUInt 1 message.algorithmicTradeIndicator
    ++ Alpha.encode message.pad1
    ++ encodeUIntLE 8 message.price
    ++ encodeUIntLE 8 message.trdRegTsTimePriority
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 4 message.trdMatchId
    ++ encodeUIntLE 4 message.lastQty
    ++ encodeUIntLE 8 message.lastPx

def decode (bytes : List UInt8) : Option (PartialOrderExecution × List UInt8) := do
  let (side, bytes) ← decodeUInt 1 bytes
  let (ordType, bytes) ← decodeUInt 1 bytes
  let (algorithmicTradeIndicator, bytes) ← decodeUInt 1 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsTimePriority, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (trdMatchId, bytes) ← decodeUIntLE 4 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  pure ({ side, ordType, algorithmicTradeIndicator, pad1, price, trdRegTsTimePriority, securityId, trdMatchId, lastQty, lastPx }, bytes)

@[simp] theorem encode_length (message : PartialOrderExecution) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : PartialOrderExecution) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PartialOrderExecution) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end PartialOrderExecution

/-- Product State Change: 16 bytes -/
structure ProductStateChange where
  tradingSessionId : BitVec 8
  tradingSessionSubId : BitVec 8
  tradSesStatus : BitVec 8
  marketCondition : BitVec 8
  fastMarketIndicator : BitVec 8
  pad3 : Alpha 3
  transactTime : BitVec 64
  deriving DecidableEq, Repr

namespace ProductStateChange

def encode (message : ProductStateChange) : List UInt8 :=
  encodeUInt 1 message.tradingSessionId
    ++ encodeUInt 1 message.tradingSessionSubId
    ++ encodeUInt 1 message.tradSesStatus
    ++ encodeUInt 1 message.marketCondition
    ++ encodeUInt 1 message.fastMarketIndicator
    ++ Alpha.encode message.pad3
    ++ encodeUIntLE 8 message.transactTime

def decode (bytes : List UInt8) : Option (ProductStateChange × List UInt8) := do
  let (tradingSessionId, bytes) ← decodeUInt 1 bytes
  let (tradingSessionSubId, bytes) ← decodeUInt 1 bytes
  let (tradSesStatus, bytes) ← decodeUInt 1 bytes
  let (marketCondition, bytes) ← decodeUInt 1 bytes
  let (fastMarketIndicator, bytes) ← decodeUInt 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ tradingSessionId, tradingSessionSubId, tradSesStatus, marketCondition, fastMarketIndicator, pad3, transactTime }, bytes)

@[simp] theorem encode_length (message : ProductStateChange) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : ProductStateChange) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ProductStateChange) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end ProductStateChange

/-- Product Summary: 16 bytes -/
structure ProductSummary where
  lastMsgSeqNumProcessed : BitVec 32
  tradingSessionId : BitVec 8
  tradingSessionSubId : BitVec 8
  tradSesStatus : BitVec 8
  marketCondition : BitVec 8
  fastMarketIndicator : BitVec 8
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace ProductSummary

def encode (message : ProductSummary) : List UInt8 :=
  encodeUIntLE 4 message.lastMsgSeqNumProcessed
    ++ encodeUInt 1 message.tradingSessionId
    ++ encodeUInt 1 message.tradingSessionSubId
    ++ encodeUInt 1 message.tradSesStatus
    ++ encodeUInt 1 message.marketCondition
    ++ encodeUInt 1 message.fastMarketIndicator
    ++ Alpha.encode message.pad7

def decode (bytes : List UInt8) : Option (ProductSummary × List UInt8) := do
  let (lastMsgSeqNumProcessed, bytes) ← decodeUIntLE 4 bytes
  let (tradingSessionId, bytes) ← decodeUInt 1 bytes
  let (tradingSessionSubId, bytes) ← decodeUInt 1 bytes
  let (tradSesStatus, bytes) ← decodeUInt 1 bytes
  let (marketCondition, bytes) ← decodeUInt 1 bytes
  let (fastMarketIndicator, bytes) ← decodeUInt 1 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ lastMsgSeqNumProcessed, tradingSessionId, tradingSessionSubId, tradSesStatus, marketCondition, fastMarketIndicator, pad7 }, bytes)

@[simp] theorem encode_length (message : ProductSummary) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : ProductSummary) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ProductSummary) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end ProductSummary

/-- Quote Request: 24 bytes -/
structure QuoteRequest where
  securityId : BitVec 64
  lastQty : BitVec 32
  side : BitVec 8
  pad3 : Alpha 3
  transactTime : BitVec 64
  deriving DecidableEq, Repr

namespace QuoteRequest

def encode (message : QuoteRequest) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 4 message.lastQty
    ++ encodeUInt 1 message.side
    ++ Alpha.encode message.pad3
    ++ encodeUIntLE 8 message.transactTime

def decode (bytes : List UInt8) : Option (QuoteRequest × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityId, lastQty, side, pad3, transactTime }, bytes)

@[simp] theorem encode_length (message : QuoteRequest) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : QuoteRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end QuoteRequest

/-- Snapshot Order: 24 bytes -/
structure SnapshotOrder where
  orderDetailsComp : OrderDetailsComp
  deriving DecidableEq, Repr

namespace SnapshotOrder

def encode (message : SnapshotOrder) : List UInt8 :=
  OrderDetailsComp.encode message.orderDetailsComp

def decode (bytes : List UInt8) : Option (SnapshotOrder × List UInt8) := do
  let (orderDetailsComp, bytes) ← OrderDetailsComp.decode bytes
  pure ({ orderDetailsComp }, bytes)

@[simp] theorem encode_length (message : SnapshotOrder) : (encode message).length = 24 := by
  unfold encode
  simp only [OrderDetailsComp.encode_length]

theorem encode_length_pos (message : SnapshotOrder) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SnapshotOrder) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [Option.bind_eq_bind]
  rw [OrderDetailsComp.decode_encode, Option.bind_some]
  rfl

end SnapshotOrder

/-- Top Of Book: 32 bytes -/
structure TopOfBook where
  transactTime : BitVec 64
  securityId : BitVec 64
  bidPx : BitVec 64
  offerPx : BitVec 64
  deriving DecidableEq, Repr

namespace TopOfBook

def encode (message : TopOfBook) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.bidPx
    ++ encodeUIntLE 8 message.offerPx

def decode (bytes : List UInt8) : Option (TopOfBook × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (bidPx, bytes) ← decodeUIntLE 8 bytes
  let (offerPx, bytes) ← decodeUIntLE 8 bytes
  pure ({ transactTime, securityId, bidPx, offerPx }, bytes)

@[simp] theorem encode_length (message : TopOfBook) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : TopOfBook) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TopOfBook) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end TopOfBook

/-- Trade Report: 40 bytes -/
structure TradeReport where
  securityId : BitVec 64
  transactTime : BitVec 64
  trdMatchId : BitVec 32
  lastQty : BitVec 32
  lastPx : BitVec 64
  matchType : BitVec 8
  matchSubType : BitVec 8
  algorithmicTradeIndicator : BitVec 8
  tradeCondition : BitVec 8
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace TradeReport

def encode (message : TradeReport) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 4 message.trdMatchId
    ++ encodeUIntLE 4 message.lastQty
    ++ encodeUIntLE 8 message.lastPx
    ++ encodeUInt 1 message.matchType
    ++ encodeUInt 1 message.matchSubType
    ++ encodeUInt 1 message.algorithmicTradeIndicator
    ++ encodeUInt 1 message.tradeCondition
    ++ Alpha.encode message.pad4

def decode (bytes : List UInt8) : Option (TradeReport × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (trdMatchId, bytes) ← decodeUIntLE 4 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (matchType, bytes) ← decodeUInt 1 bytes
  let (matchSubType, bytes) ← decodeUInt 1 bytes
  let (algorithmicTradeIndicator, bytes) ← decodeUInt 1 bytes
  let (tradeCondition, bytes) ← decodeUInt 1 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ securityId, transactTime, trdMatchId, lastQty, lastPx, matchType, matchSubType, algorithmicTradeIndicator, tradeCondition, pad4 }, bytes)

@[simp] theorem encode_length (message : TradeReport) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : TradeReport) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeReport) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end TradeReport

/-- Md Trade Entry Grp Comp: 16 bytes -/
structure MdTradeEntryGrpComp where
  mdEntryPx : BitVec 64
  mdEntrySize : BitVec 32
  mdEntryType : BitVec 8
  pad3 : Alpha 3
  deriving DecidableEq, Repr

namespace MdTradeEntryGrpComp

def encode (message : MdTradeEntryGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.mdEntryPx
    ++ encodeUIntLE 4 message.mdEntrySize
    ++ encodeUInt 1 message.mdEntryType
    ++ Alpha.encode message.pad3

def decode (bytes : List UInt8) : Option (MdTradeEntryGrpComp × List UInt8) := do
  let (mdEntryPx, bytes) ← decodeUIntLE 8 bytes
  let (mdEntrySize, bytes) ← decodeUIntLE 4 bytes
  let (mdEntryType, bytes) ← decodeUInt 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  pure ({ mdEntryPx, mdEntrySize, mdEntryType, pad3 }, bytes)

@[simp] theorem encode_length (message : MdTradeEntryGrpComp) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : MdTradeEntryGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MdTradeEntryGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end MdTradeEntryGrpComp

/-- Trade Reversal -/
structure TradeReversal where
  securityId : BitVec 64
  transactTime : BitVec 64
  trdMatchId : BitVec 32
  lastQty : BitVec 32
  lastPx : BitVec 64
  trdRegTsExecutionTime : BitVec 64
  tradeCondition : BitVec 8
  pad6 : Alpha 6
  mdTradeEntryGrpComp : Bounded 1 MdTradeEntryGrpComp
  deriving DecidableEq, Repr

namespace TradeReversal

def encode (message : TradeReversal) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 4 message.trdMatchId
    ++ encodeUIntLE 4 message.lastQty
    ++ encodeUIntLE 8 message.lastPx
    ++ encodeUIntLE 8 message.trdRegTsExecutionTime
    ++ encodeUInt 1 message.tradeCondition
    ++ Alpha.encode message.pad6
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.mdTradeEntryGrpComp.val.length)
    ++ encodeMany MdTradeEntryGrpComp.encode message.mdTradeEntryGrpComp.val

def decode (bytes : List UInt8) : Option (TradeReversal × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (trdMatchId, bytes) ← decodeUIntLE 4 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsExecutionTime, bytes) ← decodeUIntLE 8 bytes
  let (tradeCondition, bytes) ← decodeUInt 1 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  let (noMdEntries, bytes) ← decodeUInt 1 bytes
  let (mdTradeEntryGrpComp_, bytes) ← decodeMany MdTradeEntryGrpComp.decode noMdEntries.toNat bytes
  if fits_mdTradeEntryGrpComp : mdTradeEntryGrpComp_.length < 256 ^ 1 then
    pure ({ securityId, transactTime, trdMatchId, lastQty, lastPx, trdRegTsExecutionTime, tradeCondition, pad6, mdTradeEntryGrpComp := ⟨mdTradeEntryGrpComp_, fits_mdTradeEntryGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : TradeReversal) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TradeReversal) : (encode message).length ≤ 4128 := by
  have bound_mdTradeEntryGrpComp := message.mdTradeEntryGrpComp.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, encodeMany_length_const MdTradeEntryGrpComp.encode 16 MdTradeEntryGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : TradeReversal) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 MdTradeEntryGrpComp.encode MdTradeEntryGrpComp.decode MdTradeEntryGrpComp.decode_encode]
  simp only [Option.bind_some]
  simp only [message.mdTradeEntryGrpComp.length_lt, ↓reduceDIte]
  rfl

end TradeReversal

/-- Any Payload, selected by Template Id -/
inductive Payload where
  | addComplexInstrument (message : AddComplexInstrument) -- 13400
  | auctionBbo (message : AuctionBbo) -- 13500
  | auctionClearingPrice (message : AuctionClearingPrice) -- 13501
  | crossRequest (message : CrossRequest) -- 13502
  | executionSummary (message : ExecutionSummary) -- 13202
  | fullOrderExecution (message : FullOrderExecution) -- 13104
  | heartbeat (message : Heartbeat) -- 13001
  | instrumentStateChange (message : InstrumentStateChange) -- 13301
  | instrumentSummary (message : InstrumentSummary) -- 13601
  | orderAdd (message : OrderAdd) -- 13100
  | orderDelete (message : OrderDelete) -- 13102
  | orderMassDelete (message : OrderMassDelete) -- 13103
  | orderModify (message : OrderModify) -- 13101
  | orderModifySamePrio (message : OrderModifySamePrio) -- 13106
  | partialOrderExecution (message : PartialOrderExecution) -- 13105
  | productStateChange (message : ProductStateChange) -- 13300
  | productSummary (message : ProductSummary) -- 13600
  | quoteRequest (message : QuoteRequest) -- 13503
  | snapshotOrder (message : SnapshotOrder) -- 13602
  | topOfBook (message : TopOfBook) -- 13504
  | tradeReport (message : TradeReport) -- 13201
  | tradeReversal (message : TradeReversal) -- 13200
  deriving DecidableEq, Repr

namespace Payload

/-- The Template Id each message is sent under -/
def tag : Payload → BitVec 16
  | .addComplexInstrument _ => 13400
  | .auctionBbo _ => 13500
  | .auctionClearingPrice _ => 13501
  | .crossRequest _ => 13502
  | .executionSummary _ => 13202
  | .fullOrderExecution _ => 13104
  | .heartbeat _ => 13001
  | .instrumentStateChange _ => 13301
  | .instrumentSummary _ => 13601
  | .orderAdd _ => 13100
  | .orderDelete _ => 13102
  | .orderMassDelete _ => 13103
  | .orderModify _ => 13101
  | .orderModifySamePrio _ => 13106
  | .partialOrderExecution _ => 13105
  | .productStateChange _ => 13300
  | .productSummary _ => 13600
  | .quoteRequest _ => 13503
  | .snapshotOrder _ => 13602
  | .topOfBook _ => 13504
  | .tradeReport _ => 13201
  | .tradeReversal _ => 13200

def encode : Payload → List UInt8
  | .addComplexInstrument message => AddComplexInstrument.encode message
  | .auctionBbo message => AuctionBbo.encode message
  | .auctionClearingPrice message => AuctionClearingPrice.encode message
  | .crossRequest message => CrossRequest.encode message
  | .executionSummary message => ExecutionSummary.encode message
  | .fullOrderExecution message => FullOrderExecution.encode message
  | .heartbeat message => Heartbeat.encode message
  | .instrumentStateChange message => InstrumentStateChange.encode message
  | .instrumentSummary message => InstrumentSummary.encode message
  | .orderAdd message => OrderAdd.encode message
  | .orderDelete message => OrderDelete.encode message
  | .orderMassDelete message => OrderMassDelete.encode message
  | .orderModify message => OrderModify.encode message
  | .orderModifySamePrio message => OrderModifySamePrio.encode message
  | .partialOrderExecution message => PartialOrderExecution.encode message
  | .productStateChange message => ProductStateChange.encode message
  | .productSummary message => ProductSummary.encode message
  | .quoteRequest message => QuoteRequest.encode message
  | .snapshotOrder message => SnapshotOrder.encode message
  | .topOfBook message => TopOfBook.encode message
  | .tradeReport message => TradeReport.encode message
  | .tradeReversal message => TradeReversal.encode message

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 13400 then (AddComplexInstrument.decode bytes).map fun (message, rest) => (.addComplexInstrument message, rest)
  else if tag = 13500 then (AuctionBbo.decode bytes).map fun (message, rest) => (.auctionBbo message, rest)
  else if tag = 13501 then (AuctionClearingPrice.decode bytes).map fun (message, rest) => (.auctionClearingPrice message, rest)
  else if tag = 13502 then (CrossRequest.decode bytes).map fun (message, rest) => (.crossRequest message, rest)
  else if tag = 13202 then (ExecutionSummary.decode bytes).map fun (message, rest) => (.executionSummary message, rest)
  else if tag = 13104 then (FullOrderExecution.decode bytes).map fun (message, rest) => (.fullOrderExecution message, rest)
  else if tag = 13001 then (Heartbeat.decode bytes).map fun (message, rest) => (.heartbeat message, rest)
  else if tag = 13301 then (InstrumentStateChange.decode bytes).map fun (message, rest) => (.instrumentStateChange message, rest)
  else if tag = 13601 then (InstrumentSummary.decode bytes).map fun (message, rest) => (.instrumentSummary message, rest)
  else if tag = 13100 then (OrderAdd.decode bytes).map fun (message, rest) => (.orderAdd message, rest)
  else if tag = 13102 then (OrderDelete.decode bytes).map fun (message, rest) => (.orderDelete message, rest)
  else if tag = 13103 then (OrderMassDelete.decode bytes).map fun (message, rest) => (.orderMassDelete message, rest)
  else if tag = 13101 then (OrderModify.decode bytes).map fun (message, rest) => (.orderModify message, rest)
  else if tag = 13106 then (OrderModifySamePrio.decode bytes).map fun (message, rest) => (.orderModifySamePrio message, rest)
  else if tag = 13105 then (PartialOrderExecution.decode bytes).map fun (message, rest) => (.partialOrderExecution message, rest)
  else if tag = 13300 then (ProductStateChange.decode bytes).map fun (message, rest) => (.productStateChange message, rest)
  else if tag = 13600 then (ProductSummary.decode bytes).map fun (message, rest) => (.productSummary message, rest)
  else if tag = 13503 then (QuoteRequest.decode bytes).map fun (message, rest) => (.quoteRequest message, rest)
  else if tag = 13602 then (SnapshotOrder.decode bytes).map fun (message, rest) => (.snapshotOrder message, rest)
  else if tag = 13504 then (TopOfBook.decode bytes).map fun (message, rest) => (.topOfBook message, rest)
  else if tag = 13201 then (TradeReport.decode bytes).map fun (message, rest) => (.tradeReport message, rest)
  else if tag = 13200 then (TradeReversal.decode bytes).map fun (message, rest) => (.tradeReversal message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  msgSeqNum : BitVec 32
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  encodeUIntLE 2 (Payload.tag message.payload)
    ++ encodeUIntLE 4 message.msgSeqNum
    ++ Payload.encode message.payload

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (templateId, bytes) ← decodeUIntLE 2 bytes
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (payload, bytes) ← Payload.decode templateId bytes
  pure ({ msgSeqNum, payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Payload.decode_encode, Option.bind_some]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 2 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | addComplexInstrument inner =>
    have bound_inner := AddComplexInstrument.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | auctionBbo inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, AuctionBbo.encode_length]
    omega
  | auctionClearingPrice inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, AuctionClearingPrice.encode_length]
    omega
  | crossRequest inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, CrossRequest.encode_length]
    omega
  | executionSummary inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, ExecutionSummary.encode_length]
    omega
  | fullOrderExecution inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, FullOrderExecution.encode_length]
    omega
  | heartbeat inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, Heartbeat.encode_length]
    omega
  | instrumentStateChange inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, InstrumentStateChange.encode_length]
    omega
  | instrumentSummary inner =>
    have bound_inner := InstrumentSummary.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | orderAdd inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, OrderAdd.encode_length]
    omega
  | orderDelete inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, OrderDelete.encode_length]
    omega
  | orderMassDelete inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, OrderMassDelete.encode_length]
    omega
  | orderModify inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, OrderModify.encode_length]
    omega
  | orderModifySamePrio inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, OrderModifySamePrio.encode_length]
    omega
  | partialOrderExecution inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, PartialOrderExecution.encode_length]
    omega
  | productStateChange inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, ProductStateChange.encode_length]
    omega
  | productSummary inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, ProductSummary.encode_length]
    omega
  | quoteRequest inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, QuoteRequest.encode_length]
    omega
  | snapshotOrder inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, SnapshotOrder.encode_length]
    omega
  | topOfBook inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, TopOfBook.encode_length]
    omega
  | tradeReport inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, TradeReport.encode_length]
    omega
  | tradeReversal inner =>
    have bound_inner := TradeReversal.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega

/-- Size rule: Body Len counts the bytes after it plus 2, so it is written from the body and checked on decode -/
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

/-- Packet -/
structure Packet where
  packetHeader : PacketHeader
  message : List Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  PacketHeader.encode message.packetHeader
    ++ encodeMany Message.encode message.message

def decode (bytes : List UInt8) : Option Packet := do
  let (packetHeader, bytes) ← PacketHeader.decode bytes
  let message ← decodeAll Message.decode bytes.length bytes
  pure { packetHeader, message }

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [PacketHeader.encode_length, List.length_append]
  omega

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  simp only [Option.bind_eq_bind]
  rw [PacketHeader.decode_encode]
  simp only [Option.bind_some]
  rw [decodeAll_encodeMany Message.encode Message.decode Message.decode_encode Message.encode_length_pos message.message _ (encodeMany_length_ge Message.encode Message.encode_length_pos message.message), Option.bind_some]
  rfl

end Packet

end Omi.EurexT7EobiFbeV61
