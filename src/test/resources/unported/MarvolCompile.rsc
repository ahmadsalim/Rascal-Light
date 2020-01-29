module MarvolCompile

/*
 * Example Compilation of robot DSL
 * Ported from https://github.com/cwi-swat/marvo
 */
 
 // Changes: From concrete syntax to abstract syntax, elimination of comprehension, renaming and merging of datatypes, avoiding stringiness

data Dance = movePart(Part part, DanceMove move)
           | repeat(int count, Dance dance)
           | backforth(int count, Dance dance)
           | danceset(set[Dance] dances)
           | danceseq(list[Dance] dances)
           | mirror(Dance dance)
           | call(str name)
           | nop()
           | say(str speech);

data Part = arm() | legs() | elbow() | hand() | look() | arms() | elbows() | hands();

data DanceMove = up() | down() | twist() | bend() | stretch() | close() | open() | far()
               | forwards() | sideways() | inwards() | outwards() | left() | right()
               | forward() | squat() | hawaii() | luckyluke();

data LookMove
  = FarLeft()
  | Left()
  | LForward()
  | Right()
  | FarRight();

data ChinMove
  = CForward()
  | CDown()
  | CUp();

data ArmMove
  = AUp()
  | ForwardsUp()
  | Forwards()
  | ForwardsDown()
  | ADown()
  | ForwardsUpSideways()
  | ForwardsSideways()
  | ForwardsDownSideways()
  | SidewaysUp()
  | Sideways()
  | SidewaysDown();


data ArmTwistMove
  = FarInwards()
  | Inwards()
  | Outwards();

data SayMove
  = say(str uttering)
  | silence()
  ;

data ElbowMove
  = Stretch()
  | Bend();

data HandMove
  = Close()
  | Open();

data LegsMove
  = LegStretch()
  | Squat()
  | HawaiiLeft()
  | HawaiiRight()
  | LuckyLuke(); // More to come...

data BodyMove = BodyMove(
	  LookMove look,
	  ChinMove chin,
	  ArmMove leftArm, ArmMove rightArm,
	  ArmTwistMove leftArmTwist, ArmTwistMove rightArmTwist,
	  ElbowMove leftElbow, ElbowMove rightElbow,
	  HandMove leftHand, HandMove rightHand,
	  LegsMove legs,
	  SayMove mouth
	);

public BodyMove INIT_POS = BodyMove (
   LForward(),
   CForward(),
   ADown(),    ADown(),
   Inwards(), Inwards(),
   Stretch(), Stretch(),
   Close(),   Close(),
   LegStretch(),
   silence());

data SpeechOrDanceMove = speech(str v) | dancemove(DanceMove move);
data MouthOrPart = mouth() | part(Part part);

data Move = move(MouthOrPart part, set[StrOrDanceMove] moves); //Avoid stringiness here

list[BodyMove] compile(list[Dance] ds) {
  lst = [];
  for (d <- ds) {
    set[Move] ms = toMoves(d);
    BodyMove cur = INIT_POS;
    for (m <- ms)
      cur = compile(m.part, m.moves, cur);
    lst = lst + [cur];
  }
  return lst;
}

set[Move] toMoves(Dance d) {
  switch(d) {
    case say(sp): return { move(mouth(), speech(sp)) };
    case nop(): return {};
    case movePart(p,ms): {
      set[SpeechOrDanceMove] dmoves = {};
      for (m <- ms) 
        dmoves = dmoves + {dancemove(m)};
      return {move(part(p), dmoves)};
    }
    case danceset(ds): {
      set[Moves] moves = {};
      for (d <- ds)
        moves = moves + toMoves(d);
      return moves;
    }
    case mirror(d): {
      ms = {};
      for (m <- toMoves(d)) {
        if (dancemove(left()) in m.moves) {
          ms = ms + {move(m.part, m.moves - {dancemove(left())} + {dancemove(right())})};
        }
        else if (dancemove(right()) in m.moves) {
          ms = ms + {move(m.part, m.moves - {dancemove(right())} + {dancemove(left())})};
        }
        else {
          ms = ms + {m};
        }
      }
      return ms;
    }
  };
}

BodyMove compile(MouthOrPart mop, set[SpeechOrDanceMove] sods, BodyMove m) {
  switch(mop) {
    case part(arm()):
      switch(sods) {
        case {dancemove(right()), dancemove(up())}: {
          m.rightArm = AUp();
          return m;
        }
        case {dancemove(right()), dancemove(down())}: {
          m.rightArm = ADown();
          return m;
        }
        case {dancemove(right()), dancemove(forwards())}: {
          m.rightArm = Forwards();
          return m;
        }
        case {dancemove(right()), dancemove(forwards()), dancemove(up())}: {
          m.rightArm = ForwardsUp();
          return m;
        }
        case {dancemove(right()), dancemove(forwards()), dancemove(down())}: {
          m.rightArm = ForwardsDown();
          return m;
        }
        case {dancemove(right()), dancemove(forwards()), dancemove(up()), dancemove(sideways())}: {
          m.rightArm = ForwardsUpSideways();
          return m;
        }
        case {dancemove(right()), dancemove(forwards()), dancemove(down()), dancemove(sideways())}: {
          m.rightArm = ForwardsDownSideways();
          return m;
        }
        case {dancemove(right()), dancemove(forwards()), dancemove(sideways())}: {
          m.rightArm = ForwardsSideways();
          return m;
        }
        case {dancemove(right()), dancemove(sideways())}: {
          m.rightArm = Sideways();
          return m;
        }
        case {dancemove(right()), dancemove(sideways()), dancemove(up())}: {
          m.rightArm = SidewaysUp();
          return m;
        }
        case {dancemove(right()), dancemove(sideways()), dancemove(down())}: {
          m.rightArm = SidewaysDown();
          return m;
        }
        case {dancemove(right()), dancemove(twist()), dancemove(inwards())}: {
          m.rightArmTwist = Inwards();
          return m;
        }
        case {dancemove(right()), dancemove(twist()), dancemove(outwards())}: {
          m.rightArmTwist = Outwards();
          return m;
        }
        case {dancemove(right()), dancemove(twist()), dancemove(far()), dancemove(inwards())}: {
          m.rightArmTwist = FarInwards();
          return m;
        }
        case {dancemove(left()), dancemove(up())}: {
          m.leftArm = AUp();
          return m;
        }
        case {dancemove(left()), dancemove(down())}: {
          m.leftArm = ADown();
          return m;
        }
        case {dancemove(left()), dancemove(forwards())}: {
          m.leftArm = Forwards();
          return m;
        }
        case {dancemove(left()), dancemove(forwards()), dancemove(up())}: {
          m.leftArm = ForwardsUp();
          return m;
        }
        case {dancemove(left()), dancemove(forwards()), dancemove(down())}: {
          m.leftArm = ForwardsDown();
          return m;
        }
        case {dancemove(left()), dancemove(forwards()), dancemove(up()), dancemove(sideways())}: {
          m.leftArm = ForwardsUpSideways();
          return m;
        }
        case {dancemove(left()), dancemove(forwards()), dancemove(down()), dancemove(sideways())}: {
          m.leftArm = ForwardsDownSideways();
          return m;
        }
        case {dancemove(left()), dancemove(forwards()), dancemove(sideways())}: {
          m.leftArm = ForwardsSideways();
          return m;
        }
        case {dancemove(left()), dancemove(sideways())}: {
          m.leftArm = Sideways();
          return m;
        }
        case {dancemove(left()), dancemove(sideways()), dancemove(up())}: {
          m.leftArm = SidewaysUp();
          return m;
        }
        case {dancemove(left()), dancemove(sideways()), dancemove(down())}: {
          m.leftArm = SidewaysDown();
          return m;
        }
        case {dancemove(left()), dancemove(twist()), dancemove(inwards())}: {
          m.leftArmTwist = Inwards();
          return m;
        }
        case {dancemove(left()), dancemove(twist()), dancemove(outwards())}: {
          m.leftArmTwist = Outwards();
          return m;
        }
        case {dancemove(left()), dancemove(twist()), dancemove(far()), dancemove(inwards())}: {
          m.leftArmTwist = FarInwards();
          return m;
        }
      }
    case part(elbow()):
      switch(sods) {
        case {dancemove(right()), dancemove(stretch())}: {
          m.rightElbow = Stretch();
          return m;
        }
        case {dancemove(right()), dancemove(bend())}: {
          m.rightElbow = Bend();
          return m;
        }
        case {dancemove(left()), dancemove(stretch())}: {
          m.leftElbow = Stretch();
          return m;
        }
        case {dancemove(left()), dancemove(bend())}: {
          m.leftElbow = Bend();
          return m;
        }
      }
    case part(hand()):
      switch(sods) {
        case {dancemove(right()), dancemove(open())}: {
          m.rightHand = Open();
          return m;
        }
        case {dancemove(right()), dancemove(close())}: {
          m.rightHand = Close();
          return m;
        }
        case {dancemove(left()), dancemove(open())}: {
          m.leftHand = Open();
          return m;
        }
        case {dancemove(left()), dancemove(close())}: {
          m.leftHand = Close();
          return m;
        }
      }
    case part(chin()):
      switch(sods) {
        case {dancemove(forward())}: {
          m.chin = CForward();
          return m;
        }
        case {dancemove(up())}: {
          m.chin = CUp();
          return m;
        }
        case {dancemove(down())}: {
          m.chin = CDown();
          return m;
        }
      }
    case part(legs()):
      switch(sods) {
        case {dancemove(forward())}: {
          m.legs = Stretch();
          return m;
        }
        case {dancemove(squat())}: {
          m.legs = Squat();
          return m;
        }
        case {dancemove(hawaii()), dancemove(left())}: {
          m.legs = HawaiiLeft();
          return m;
        }
        case {dancemove(hawaii()), dancemove(right())}: {
          m.legs = HawaiiRight();
          return m;
        }
        case {dancemove(luckyluke())}: {
          m.legs = LuckyLuke();
          return m;
        }
      }
    case part(look()):
      switch(sods) {
        case {dancemove(far()), dancemove(left())}: {
          m.look = FarLeft();
          return m;
        }
        case {dancemove(far()), dancemove(right())}: {
          m.look = FarRight();
          return m;
        }
        case {dancemove(left())}: {
          m.look = Left();
          return m;
        }
        case {dancemove(right())}: {
          m.look = Right();
          return m;
        }
        case {dancemove(forward())}: {
          m.look = LForward();
          return m;
        }
      }
    case mouth(): 
      switch(sods) {
        case {speech(uttering)}: {
          m.mouth=say(uttering);
          return m;
        }
      }
  };
}