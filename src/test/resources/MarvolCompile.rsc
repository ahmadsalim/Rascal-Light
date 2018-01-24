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
  | Down()
  | Up();

data ArmMove
  = Up()
  | ForwardsUp()
  | Forwards()
  | ForwardsDown()
  | Down()
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

alias BodyPosition = BodyMove;

public BodyPosition INIT_POS = BodyMove (
   LForward(),
   CForward(),
   ArmMove::Down(),    ArmMove::Down(),
   Inwards(), Inwards(),
   Stretch(), Stretch(),
   Close(),   Close(),
   LegStretch(),
   silence());

data StrOrDanceMove = strval(str v) | dancemove(DanceMove move);
data MouthOrPart = mouth() | part(Part part);

data Move = move(MouthOrPart part, set[StrOrDanceMove] moves); //Avoid stringiness here

list[BodyMove] compile(list[Dance] ds) {
  lst = [];
  for (d <- ds) {
    cur = INIT_POS;
    ms = toMoves(d);
    cur = ( cur | compile(m.part, m.moves, it) | m <- ms );
    lst += [cur];
  }
  return lst;
}


set[Move] toMoves(say(sp)) = {<"mouth", sp>};
set[Move] toMoves(nop()) = {};
set[Move] toMoves(movePart(p, ms)) = {<"<p>", { "<m>" | m <- ms }>};
set[Move] toMoves(danceset(ds)) = ( {} | it + toMoves(d) | d <- ds );
set[Move] toMoves(mirror(d)) {
  ms = {};
  for (m <- toMoves(d)) {
    if ("left" in m.moves) {
      ms += {<m.part, m.moves - {"left"} + {"right"}>};
    }
    else if ("right" in m.moves) {
      ms += {<m.part, m.moves - {"right"} + {"left"}>};
    }
    else {
      ms += {m};
    }
  }
  return ms;
}

BodyMove compile("arm", {"right", "up"}, BodyMove m) = m[rightArm=ArmMove::Up()];
BodyMove compile("arm", {"right", "down"} , BodyMove m) = m[rightArm=ArmMove::Down()];
BodyMove compile("arm", {"right", "forwards"} , BodyMove m) = m[rightArm=Forwards()];
BodyMove compile("arm", {"right", "forwards", "up"} , BodyMove m) = m[rightArm=ForwardsUp()];
BodyMove compile("arm", {"right", "forwards", "down"} , BodyMove m) = m[rightArm=ForwardsDown()];
BodyMove compile("arm", {"right", "forwards", "up", "sideways"} , BodyMove m) = m[rightArm=ForwardsUpSideways()];
BodyMove compile("arm", {"right", "forwards", "down", "sideways"} , BodyMove m) = m[rightArm=ForwardsDownSideways()];
BodyMove compile("arm", {"right", "forwards", "sideways"} , BodyMove m) = m[rightArm=ForwardsSideways()];
BodyMove compile("arm", {"right", "sideways"} , BodyMove m) = m[rightArm=Sideways()];
BodyMove compile("arm", {"right", "sideways", "up"} , BodyMove m) = m[rightArm=SidewaysUp()];
BodyMove compile("arm", {"right", "sideways", "down"} , BodyMove m) = m[rightArm=SidewaysDown()];

BodyMove compile("arm", {"right", "twist", "inwards"} , BodyMove m) = m[rightArmTwist=Inwards()];
BodyMove compile("arm", {"right", "twist", "outwards"} , BodyMove m) = m[rightArmTwist=Outwards()];
BodyMove compile("arm", {"right", "twist", "far", "inwards"} , BodyMove m) = m[rightArmTwist=FarInwards()];

BodyMove compile("arm", {"left", "up"}, BodyMove m) = m[leftArm=ArmMove::Up()];
BodyMove compile("arm", {"left", "down"} , BodyMove m) = m[leftArm=ArmMove::Down()];
BodyMove compile("arm", {"left", "forwards"} , BodyMove m) = m[leftArm=Forwards()];
BodyMove compile("arm", {"left", "forwards", "up"} , BodyMove m) = m[leftArm=ForwardsUp()];
BodyMove compile("arm", {"left", "forwards", "down"} , BodyMove m) = m[leftArm=ForwardsDown()];
BodyMove compile("arm", {"left", "forwards", "up", "sideways"} , BodyMove m) = m[leftArm=ForwardsUpSideways()];
BodyMove compile("arm", {"left", "forwards", "down", "sideways"} , BodyMove m) = m[leftArm=ForwardsDownSideways()];
BodyMove compile("arm", {"left", "forwards", "sideways"} , BodyMove m) = m[leftArm=ForwardsSideways()];
BodyMove compile("arm", {"left", "sideways"} , BodyMove m) = m[leftArm=Sideways()];
BodyMove compile("arm", {"left", "sideways", "up"} , BodyMove m) = m[leftArm=SidewaysUp()];
BodyMove compile("arm", {"left", "sideways", "down"} , BodyMove m) = m[leftArm=SidewaysDown()];

BodyMove compile("arm", {"left", "twist", "inwards"} , BodyMove m) = m[leftArmTwist=Inwards()];
BodyMove compile("arm", {"left", "twist", "outwards"} , BodyMove m) = m[leftArmTwist=Outwards()];
BodyMove compile("arm", {"left", "twist", "far", "inwards"} , BodyMove m) = m[leftArmTwist=FarInwards()];



BodyMove compile("elbow", {"right", "stretch"}, BodyMove m) = m[rightElbow=Stretch()];
BodyMove compile("elbow", {"right", "bend"}, BodyMove m) = m[rightElbow=Bend()];

BodyMove compile("hand", {"right", "open"}, BodyMove m) = m[rightHand=Open()];
BodyMove compile("hand", {"right", "close"}, BodyMove m) = m[rightHand=Close()];

BodyMove compile("elbow", {"left", "stretch"}, BodyMove m) = m[leftElbow=Stretch()];
BodyMove compile("elbow", {"left", "bend"}, BodyMove m) = m[leftElbow=Bend()];

BodyMove compile("hand", {"left", "open"}, BodyMove m) = m[leftHand=Open()];
BodyMove compile("hand", {"left", "close"}, BodyMove m) = m[leftHand=Close()];

BodyMove compile("chin", {"forward"}, BodyMove m) = m[chin=CForward()];
BodyMove compile("chin", {"up"}, BodyMove m) = m[chin=ChinMove::Up()];
BodyMove compile("chin", {"down"}, BodyMove m) = m[chin=ChinMove::Down()];

BodyMove compile("legs", {"forward"}, BodyMove m) = m[legs=Stretch()];
BodyMove compile("legs", {"squat"}, BodyMove m) = m[legs=Squat()];
BodyMove compile("legs", {"hawaii", "left"}, BodyMove m) = m[legs=HawaiiLeft()];
BodyMove compile("legs", {"hawaii", "right"}, BodyMove m) = m[legs=HawaiiRight()];
BodyMove compile("legs", {"luckyluke"}, BodyMove m) = m[legs=LuckyLuke()];

BodyMove compile("look", {"far", "left"}, BodyMove m) = m[look=FarLeft()];
BodyMove compile("look", {"far", "right"}, BodyMove m) = m[look=FarRight()];
BodyMove compile("look", {"left"}, BodyMove m) = m[look=Left()];
BodyMove compile("look", {"right"}, BodyMove m) = m[look=Right()];
BodyMove compile("look", {"forward"}, BodyMove m) = m[look=LForward()];
BodyMove compile("mouth", {str uttering}, BodyMove m) = m[mouth=say(uttering)];