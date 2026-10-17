"use strict";

interface KDPointCostSource extends KDPoint {
	/**  g = cost  */
	g: number;
	/**  f = cost with heuristic  */
	f: number;
	/**  s = source  */
	s: string;
};

let KDPathCache: Map<string, KDPoint[]> = new Map();

let KDPathCacheIgnoreLocks: Map<string, KDPoint[]> = new Map();

let KDSmartMovable = new Map();
let KDMovable = new Map();

function KDUpdateDoorNavMap() {
	KDPathCache = new Map();
	KDUpdateChokes = true;
	KDMovable = new Map();
	KDSmartMovable = new Map();
}

/**
 * @param x
 * @param y
 */
function KDIsMovable(x: number, y: number): boolean {
	if (KDMovable.has(x+','+y)) {
		return KDMovable.get(x+','+y);
	} else {
		let m = KinkyDungeonMovableTilesEnemy.includes(KinkyDungeonMapGet(x, y));
		KDMovable.set(x+','+y, m);
		return m;
	}
}

/**
 * @param x
 * @param y
 */
function KDIsSmartMovable(x: number, y: number): boolean {
	if (KDSmartMovable.has(x+','+y)) {
		return KDSmartMovable.get(x+','+y);
	} else {
		let m = KinkyDungeonMovableTilesSmartEnemy.includes(KinkyDungeonMapGet(x, y));
		KDSmartMovable.set(x+','+y, m);
		return m;
	}
}

let KDPathfindingCacheHits = 0;
let KDPathfindingCacheFails = 0;

let KDPFTrim = 40;

/** When true, restores the legacy (iteration-order dependent)
 * diagonal-smoothing direction; default uses the true predecessor instead. */
let KDPathLegacyDir = false;

/** Reusable binary min-heap backing the A* open set.
 * Stores (f, key) pairs where key indexes into the `open` Map.
 * Duplicate keys are allowed (lazy deletion); stale entries are skipped on pop.
 * Call kdHeapClear() before each pathfinding run.
 * NOT re-entrant: KinkyDungeonFindPath must not be called recursively.
 * (Verified: no callback reachable from the search loop re-enters pathfinding.) */
let KDHeapF: number[] = [];
let KDHeapKey: string[] = [];
let KDHeapSize = 0;

function kdHeapClear(): void {
	KDHeapSize = 0;
}

/** Fully release the heap's backing arrays. Called when the map changes so that
 * no data (including retained key strings) carries over between maps.
 * Not required for correctness: kdHeapClear() runs at every search start. */
function KDResetPathfindingHeap(): void {
	KDHeapF.length = 0;
	KDHeapKey.length = 0;
	KDHeapSize = 0;
}

function kdHeapPush(f: number, key: string): void {
	let i = KDHeapSize++;
	KDHeapF[i] = f;
	KDHeapKey[i] = key;
	while (i > 0) {
		let p = (i - 1) >> 1;
		if (KDHeapF[p] <= KDHeapF[i]) break;
		let tf = KDHeapF[p]; KDHeapF[p] = KDHeapF[i]; KDHeapF[i] = tf;
		let tk = KDHeapKey[p]; KDHeapKey[p] = KDHeapKey[i]; KDHeapKey[i] = tk;
		i = p;
	}
}

function kdHeapPop(): string {
	let topKey = KDHeapKey[0];
	KDHeapSize--;
	if (KDHeapSize > 0) {
		KDHeapF[0] = KDHeapF[KDHeapSize];
		KDHeapKey[0] = KDHeapKey[KDHeapSize];
		let i = 0;
		while (true) {
			let l = 2 * i + 1, r = l + 1, m = i;
			if (l < KDHeapSize && KDHeapF[l] < KDHeapF[m]) m = l;
			if (r < KDHeapSize && KDHeapF[r] < KDHeapF[m]) m = r;
			if (m === i) break;
			let tf = KDHeapF[m]; KDHeapF[m] = KDHeapF[i]; KDHeapF[i] = tf;
			let tk = KDHeapKey[m]; KDHeapKey[m] = KDHeapKey[i]; KDHeapKey[i] = tk;
			i = m;
		}
	}
	return topKey;
}

/** Default A* heuristic hoisted to module scope. */
function KDDefaultHeuristic(xx: number, yy: number, endxx: number, endyy: number): number {
	return 0.1*KDistEuclideanApprox((xx - endxx) * (xx - endxx), (yy - endyy) * (yy - endyy));
}

function KDWiredDoorPathable(triggerX: number, triggerY: number, tile?: string, doorX?: number, doorY?: number, ): boolean {
	if (triggerX == doorX && triggerY == doorY) {
		// a trigger on top of the door would be unreachable
		return false;
	}

	const door = tile || KinkyDungeonTilesGet(`${doorX},${doorY}`);
	switch (door?.wireType) {
	case "AutoDoor_HoldOpen":
	case "AutoDoor_Open":
		break;
	default:
		// not a supported door
		return false;
	}
	let effects = KDEffectTileTags(triggerX, triggerY);
	if (!effects.wire) {
		// door is adjacent to a trigger but not wired to it
		return false;
	}

	// find a directly-adjacent door trigger
	return !!effects.pathplate;
}

/**
 * @param startx - the start position
 * @param starty - the start position
 * @param endx - the end positon
 * @param endy - the end positon
 * @param blockEnemy - Do enemies block movement?
 * @param blockPlayer - Does player block movement?
 * @param ignoreLocks
 * @param Tiles - Allowed move tiles!
 * @param [RequireLight]
 * @param [noDoors]
 * @param [needDoorMemory]
 * @param [Enemy] - Enemy trying to pathfind
 * @param [trimLongDistance] - Give up after 1000 or so tiles checked
 * @param [heuristicOverride]
 * @param [taxicab]
 * @param [ignoreTrafficLaws]
 */
function KinkyDungeonFindPath (
	startx:              number,
	starty:              number,
	endx:                number,
	endy:                number,
	blockEnemy:          boolean,
	blockPlayer:         boolean,
	ignoreLocks:         boolean,
	Tiles:               string,
	RequireLight?:       boolean,
	noDoors?:            boolean,
	needDoorMemory?:     boolean,
	Enemy?:              entity,
	trimLongDistance?:   boolean,
	heuristicOverride?:  (x: number, y: number, xx: number, yy: number) => number,
	taxicab?:            boolean,
	ignoreTrafficLaws?:  boolean,
	allowPassable?:  	 boolean,
	ignoreAllWeighting?: boolean,
	/** can swap with things leashed with the same */
	Leashtarget?: number,
	RequireFog?: boolean,
	EnemyWeight?: number
): KDPoint[]
{
	let tileShort = Tiles;
	if (Tiles == KinkyDungeonMovableTilesSmartEnemy) tileShort = "TSE";
	else if (Tiles == KinkyDungeonMovableTilesEnemy) tileShort = "TE";
	else if (Tiles == KinkyDungeonGroundTiles) tileShort = "TG";
	let index = `${startx},${starty},${endx},${endy},${tileShort}`;
	if (!blockEnemy && !blockPlayer && !RequireLight && !RequireFog && !noDoors && !needDoorMemory) {
		if (ignoreLocks) {
			if (KDPathCacheIgnoreLocks.has(index)) {
				KDPathfindingCacheHits++;
				if (KDPathCacheIgnoreLocks.get(index)[0] && KDistChebyshev(KDPathCacheIgnoreLocks.get(index)[0].x - startx, KDPathCacheIgnoreLocks.get(index)[0].y - starty) < 1.5)
					return KDPathCacheIgnoreLocks.get(index).slice(0);
				else KDPathCacheIgnoreLocks.delete(index);
			}
		} else {
			if (KDPathCache.has(index)) {
				KDPathfindingCacheHits++;
				if (KDPathCache.get(index)[0] && KDistChebyshev(KDPathCache.get(index)[0].x - startx, KDPathCache.get(index)[0].y - starty) < 1.5)
					return KDPathCache.get(index).slice(0);
				else KDPathCache.delete(index);
			}
		}

	}

	if (KDistChebyshev(startx - endx, starty - endy) < 1.5) {
		return [{x: endx, y: endy}];
	}

	let heur = heuristicOverride || KDDefaultHeuristic;
	// g = cost
	// f = cost with heuristic
	// s = source
	let TilesTemp = Tiles;
	if (noDoors) TilesTemp = Tiles.replace("D", "");
	let start: KDPointCostSource = {x: startx, y: starty, g: 0, f: 0, s: ""};

	// We generate a grid based on map size
	let open: Map<string, KDPointCostSource> = new Map();
	let closed: Map<string, KDPointCostSource> = new Map();
	kdHeapClear();
	let startKey = startx + "," + starty;
	open.set(startKey, start);
	kdHeapPush(start.f, startKey);

	let costBonus = 0;
	let MapTile = null;
	let moveCost = 1;
	let xx = 0;
	let yy = 0;
	let loc = "";
	/** non-smart enemies that cant usedoors won't path through autodoors either
	 * TBD on whether I want this sort of behavior- 
	 * Also if there is an Enemy that is flying, it won't path through autodoors since pressureplates don't trigger on flying
	 * Again TBD since I feel like levitating enemies should be able to press those
	*/
	let allowWiredDoors = TilesTemp.includes('D') && (!Enemy || !KDIsFlying(Enemy)); 

	while(open.size > 0) {
		// Trim if it takes too long
		if (trimLongDistance && (closed.size > KDPFTrim || open.size > 3*KDPFTrim)) {
			console.log("Quit pathfinding");
			return undefined; // Give up
		}
		let dx = 0;
		let dy = 0;
		// Get the open tile with the lowest weight (binary heap + lazy deletion)
		let lowLoc = kdHeapPop();
		let lowest: KDPointCostSource = open.get(lowLoc);
		// Skip stale heap entries (node was improved & re-pushed, or already closed)
		if (!lowest || closed.has(lowLoc)) continue;
		// Use the true predecessor for the diagonal-smoothing direction.
		let lowest_old: KDPointCostSource = KDPathLegacyDir ? undefined : closed.get(lowest.s);
		moveCost = 1;
			// Check bordering tiles on the lowest
			for (let x = -1; x <= 1; x++) {
				for (let y = -1; y <= 1; y++) {
					if ((x != 0 || y != 0) && (!taxicab || y == 0 || x == 0)) {
						xx = lowest.x + x;
						yy = lowest.y + y;
						loc = (xx) + "," + (yy)
						let tile = (xx == endx && yy == endy) ? "" : KinkyDungeonMapGet(xx, yy);
						MapTile = KinkyDungeonTilesGet(loc);
						let locIndex = `${lowLoc},${endx},${endy},${tileShort}`;
						const useWiredDoor = allowWiredDoors && KDWiredDoorPathable(lowest.x, lowest.y, tile);
						// If we have found the end
						if (xx == endx && yy == endy) {
							closed.set(lowLoc, lowest);
							let newPath = KinkyDungeonGetPath(closed, lowest.x, lowest.y, endx, endy);
							if (!blockEnemy && !blockPlayer && !RequireLight && !RequireLight && !noDoors && !needDoorMemory) {
								if (ignoreLocks) {
									if (!KDPathCacheIgnoreLocks.has(index)) KDSetPathfindCache(KDPathCacheIgnoreLocks, newPath, endx, endy, tileShort, index);
								} else {
									if (!KDPathCache.has(index)) KDSetPathfindCache(KDPathCache, newPath, endx, endy, tileShort, index);
								}
							}
							KDPathfindingCacheFails++;
							if (newPath.length > 0 && TilesTemp.includes(KinkyDungeonMapGet(newPath[0].x, newPath[0].y)))
								return newPath;
							else return undefined;
						} else if (!blockEnemy && !blockPlayer && !RequireLight && !RequireLight && !noDoors && !needDoorMemory
								&& ((ignoreLocks && KDPathCacheIgnoreLocks.has(locIndex)) || (!ignoreLocks && KDPathCache.has(locIndex)))) {
							let newPath = [];
							if (ignoreLocks) {
								closed.set(lowLoc, lowest);
								newPath = KinkyDungeonGetPath(closed, lowest.x, lowest.y);
								let endPath = KDPathCacheIgnoreLocks.get(locIndex).slice(0);
								KDPathfindingCacheHits++;
								newPath.push(...endPath);
							} else {
								closed.set(lowLoc, lowest);
								newPath = KinkyDungeonGetPath(closed, lowest.x, lowest.y);
								let endPath = KDPathCache.get(locIndex).slice(0);
								KDPathfindingCacheHits++;
								newPath.push(...endPath);
							}
							if (newPath.length > 0) {
								if (newPath[0] && KDistChebyshev(newPath[0].x - startx, newPath[0].y - starty) < 1.5) {
									if (ignoreLocks) {
										if (!KDPathCacheIgnoreLocks.has(index)) KDSetPathfindCache(KDPathCacheIgnoreLocks, newPath, endx, endy, tileShort, index);
									} else {
										if (!KDPathCache.has(index)) KDSetPathfindCache(KDPathCache, newPath, endx, endy, tileShort, index);
									}
									return newPath;
								}
								else if (ignoreLocks) {
									KDPathCacheIgnoreLocks.delete(locIndex);
								} else {
									KDPathCache.delete(locIndex);
								}
							} else return undefined;
						}
						// Give up and add to the test array
						else if ((TilesTemp.includes(tile) || useWiredDoor)
							&& (!RequireLight || KinkyDungeonVisionGet(xx, yy) > 0)
							&& (!RequireFog || KinkyDungeonVisionGet(xx, yy) > 0 || KinkyDungeonFogGet(xx, yy) > 0)
							&& (ignoreLocks || !MapTile || !MapTile.Lock || (Enemy && KDLocks[MapTile.Lock].canNPCPass(xx, yy, MapTile, Enemy)))
							&& (!KinkyDungeonEnemyAt(xx, yy)?.Enemy?.immobile)
							&& (!blockEnemy || !!EnemyWeight
								|| ((needDoorMemory && KinkyDungeonVisionGet(xx, yy) <= 0.1)
									|| ((Leashtarget > 0 && Leashtarget == KinkyDungeonEnemyAt(xx, yy)?.leash?.entity)
									|| KinkyDungeonNoEnemyExceptSub(xx, yy, false, Enemy)
									|| (allowPassable && KDCanPassEnemy(KDPlayer(), KinkyDungeonEnemyAt(xx, yy))))))
							&& (!blockPlayer || KinkyDungeonPlayerEntity.x != xx || KinkyDungeonPlayerEntity.y != yy)
							&& (!needDoorMemory || tile != "d" || KDOpenDoorTiles.includes(KDMapData.TilesMemory[xx + "," + yy]) || useWiredDoor)) {
							costBonus = 0;
							if (EnemyWeight) {
								if (!(((needDoorMemory && KinkyDungeonVisionGet(xx, yy) <= 0.1)
									|| ((Leashtarget > 0 && Leashtarget == KinkyDungeonEnemyAt(xx, yy)?.leash?.entity)
									|| KinkyDungeonNoEnemyExceptSub(xx, yy, false, Enemy)
									|| (allowPassable && KDCanPassEnemy(KDPlayer(), KinkyDungeonEnemyAt(xx, yy))))))) {
										costBonus += EnemyWeight;
									}
							}
							if (!ignoreTrafficLaws && !ignoreAllWeighting) {
								if (KDEffectTileTagsLoc(loc)?.danger) costBonus += 12;
								if (Enemy) {
									if (KDTileSlows(Enemy, xx, yy)) costBonus += 3;
								}
								else if (tile == "V" && !(MapTile?.Sfty)) costBonus = 14;
								else if (tile == "N") costBonus = 30;
								else if (tile == "D") costBonus = 2.5;
								else if (tile == "g") costBonus = 5;
								else if (tile == "L") costBonus = 4;
								else if (tile == "T") costBonus = 2;
								costBonus = (MapTile && MapTile.Lock) ? costBonus + 2 : costBonus;
								costBonus = (MapTile && MapTile.OL) ? costBonus + 12 : costBonus;
								costBonus = (KDMapData.Traffic?.length > 0 && KDMapData.Traffic[yy])
									? costBonus + (KDMapData.Traffic[yy][xx] || 0) : costBonus;
								costBonus = Math.max(0, costBonus);
							} else if (!ignoreAllWeighting) {
								if (tile == "V" && !(MapTile?.Sfty)) costBonus = 3;
								else if (tile == "N") costBonus = 8;
								else if (tile == "L") costBonus = 2;
							}
							// when moving diagonally we penalize if we werent moving diagonally before
							// this is to help avoid weird zigzag patterns when realistically an enemy should walk straight thru a room
							if (!!x && !!y) {
								if (lowest_old) {
									dx = lowest.x-lowest_old.x;
									dy = lowest.y-lowest_old.y;
									if (dx != x || dy != y) {
										costBonus += 0.41;
									} else costBonus += 0.1;
								} else {
									costBonus += 0.4;
								}
							}
							let q = xx + "," + yy;
							let succ: KDPointCostSource = {x: xx, y: yy,
								g: moveCost + costBonus + lowest.g,
								f: moveCost + costBonus + lowest.g + heur(xx, yy, endx, endy),
								s: lowLoc};
							let openSucc = open.get(q);
							if (!openSucc || openSucc.f > succ.f) {
								let closedSucc = closed.get(q);
								if (!closedSucc || closedSucc.f > succ.f) {
									open.set(q, succ);
									// Lazy deletion: duplicate heap entries are fine
									kdHeapPush(succ.f, q);
								}
							}
						}
					}
				}
			}
		open.delete(lowLoc);

		closed.set(lowLoc, lowest);
	}

	return undefined;
}

// Goes back and gets path backwards from xx, adding endx and endy
function KinkyDungeonGetPath(closed: Map<string, KDPointCostSource>, xx: number, yy: number, endx?: number, endy?: number): KDPoint[] {
	let list = [];
	if (endx && endy) list.push({x: endx, y: endy});

	let current = closed.get(xx + "," + yy);
	while (current) {
		if (current.s) {
			list.push({x: current.x, y: current.y});
			current = closed.get(current.s);
		} else current = undefined;
	}

	return list.reverse();
}

/**
 * @param PathMap
 * @param newPath
 * @param endx
 * @param endy
 * @param Tiles
 * @param Finalindex
 */
function KDSetPathfindCache(PathMap: Map<string, KDPoint[]>, newPath: KDPoint[], endx: number, endy: number, Tiles: string, Finalindex: string): void {
	for (let i = 0; i < newPath.length - 1; i++) {
		let path = newPath.slice(i);
		let index = `${path[0].x},${path[0].y},${endx},${endy},${Tiles}`;
		PathMap.set(index, path.slice(1));
	}
	if (Finalindex)
		PathMap.set(Finalindex, newPath.slice(0));
}
