module MarvolCompile

/*
 * Example Compilation of robot DSL
 * Ported from https://github.com/cwi-swat/marvo
 */

start syntax Program = Definition* defs Dance main;

syntax Definition = "def" Id name "=" Dance dance;

lexical Speech = "\"" ![\n\r\"]* text "\"";

syntax Dance
  = Part Move+ ";"
  | "repeat" Nat Dance
  | "backforth" Nat Dance
  | @Foldable "{" Dance* "}"
  | @Foldable "{|" Dance* "|}"
  | "mirror" Dance
  | @category="Identifier" call: Id name ";"
  | "nop" ";"
  | "say" Speech speech ";"?
  ;

syntax Part
  = "arm"
  | "legs"
  | "elbow"
  | "hand"
  | "chin"
  | "look"
  | "arms"
  | "elbows"
  | "hands"
  ;

syntax Move
  = @category="Constant" "up"
  | @category="Constant" "down"
  | @category="Constant" "twist"
  | @category="Constant" "bend"
  | @category="Constant" "stretch"
  | @category="Constant" "close"
  | @category="Constant" "open"
  | @category="Constant" "far"
  | @category="Constant" "forwards"
  | @category="Constant" "sideways"
  | @category="Constant" "inwards"
  | @category="Constant" "outwards"
  | @category="Constant" "left"
  | @category="Constant" "right"
  | @category="Constant" "forward"
  | @category="Constant" "squat"
  | @category="Constant" "hawaii"
  | @category="Constant" "luckyluke"
  ;

keyword Reserved
	= "repeat" | "backforth" | "mirror" | "nop"
	;

keyword Reserved
	= "arm" | "legs" | "elbow" | "hand" | "chin" | "look" | "arms" | "elbows" | "hands"
	;

keyword Reserved
	= "up" | "down" | "twist" | "bend" | "stretch" | "close" |  "open" |  "far"
	| "forwards" | "sideways" | "inwards" | "outwards" | "left" | "right" | "forward" | "squat"
 	| "hawaii" | "luckyluke";

lexical Id = ([a-zA-Z_] !<< [a-zA-Z_][a-zA-Z0-9_]* !>> [a-zA-Z0-9_]) \ Reserved;

lexical Nat = [0-9]+ !>> [0-9];

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

alias Move = tuple[str part, set[str] moves];

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

set[Move] toMoves((Dance) `say <Speech sp>`) = {<"mouth", {"<sp.text>"}>};
set[Move] toMoves((Dance) `say <Speech sp>;`) = {<"mouth", {"<sp.text>"}>};

set[Move] toMoves((Dance)`nop;`) = {};

set[Move] toMoves((Dance)`<Part p> <Move+ ms>;`)
  = {<"<p>", { "<m>" | m <- ms }>};

set[Move] toMoves((Dance)`{|<Dance* ds>|}`)
  = ( {} | it + toMoves(d) | d <- ds, bprintln("D = <d>") );


set[Move] toMoves((Dance)`mirror <Dance d>`) {
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


/* Unfortunate heavy coupling with Config. */
/* Todo: allow twists with forward etc. */

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
