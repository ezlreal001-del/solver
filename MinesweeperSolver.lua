local MINE_THRESHOLD = 0.7;
local SAFE_THRESHOLD = 0.3;
local USE_PATTERNS = true;
local MINE_COUNT = 100;
local MAX_COMP_SIZE = 32;
local SOLUTION_LIMIT = 10000000;
local board = {cells={},revealed={},flagged={},cleared={},probs={},rows={},flat={}};
local state = {cx=nil,cz=nil,folder=nil,partCount=0,partHash="",tick=0,lastTick=-1};
local cols, rows = 0, 0;
local abs, floor, huge = math.abs, math.floor, math.huge;
local min, max, sort = math.min, math.max, table.sort;
local function toKey(x, z)
	return x .. ":" .. z;
end
local function isNum(s)
	return tonumber(s) ~= nil;
end
local function stillHidden(c)
	local FlatIdent_52901 = 0;
	while true do
		if (FlatIdent_52901 == 1) then
			return c.hidden == true;
		end
		if (FlatIdent_52901 == 0) then
			if not c then
				return false;
			end
			if (c.kind == "clue") then
				return false;
			end
			FlatIdent_52901 = 1;
		end
	end
end
local RED = Color3.fromRGB(255, 60, 60);
local RED_DIM = Color3.fromRGB(255, 160, 160);
local MINT = Color3.fromRGB(60, 255, 140);
local MINT_DIM = Color3.fromRGB(160, 255, 200);
local HOT_RED = Color3.fromRGB(255, 80, 80);
local HOT_RED2 = Color3.fromRGB(255, 160, 160);
local SKY = Color3.fromRGB(80, 220, 255);
local SKY_DIM = Color3.fromRGB(160, 235, 255);
local AMBER = Color3.fromRGB(255, 200, 50);
local AMBER_DIM = Color3.fromRGB(255, 225, 140);
local BLACK = Color3.fromRGB(0, 0, 0);
local b32 = type(bit32) == "table";
local blib = type(bit) == "table";
local band, rshift, bnot, bor, lshift;
if b32 then
	band = bit32.band;
	rshift = bit32.rshift;
	bnot = bit32.bnot;
	bor = bit32.bor;
	lshift = bit32.lshift;
elseif blib then
	band = bit.band;
	rshift = bit.rshift;
	bnot = bit.bnot;
	bor = bit.bor;
	lshift = bit.lshift;
end
local fmask = nil;
local function buildMasks(sz, lists)
	local FlatIdent_2953F = 0;
	local masks;
	while true do
		if (FlatIdent_2953F == 0) then
			masks = {};
			if (band and bor and lshift and (sz <= 32)) then
				local FlatIdent_2FBEB = 0;
				while true do
					if (FlatIdent_2FBEB == 1) then
						return masks, "n";
					end
					if (FlatIdent_2FBEB == 0) then
						fmask = ((sz < 32) and ((2 ^ sz) - 1)) or 4294967295;
						for i = 1, #lists do
							local FlatIdent_63487 = 0;
							local m;
							while true do
								if (FlatIdent_63487 == 0) then
									m = 0;
									for _, j in ipairs(lists[i]) do
										m = bor(m, lshift(1, j - 1));
									end
									FlatIdent_63487 = 1;
								end
								if (FlatIdent_63487 == 1) then
									masks[i] = m;
									break;
								end
							end
						end
						FlatIdent_2FBEB = 1;
					end
				end
			elseif band then
				local FlatIdent_8199B = 0;
				while true do
					if (FlatIdent_8199B == 0) then
						fmask = nil;
						for i = 1, #lists do
							local a = {};
							for _, j in ipairs(lists[i]) do
								local FlatIdent_5ED46 = 0;
								local c;
								local b;
								while true do
									if (FlatIdent_5ED46 == 1) then
										a[c] = bor(a[c] or 0, lshift(1, b));
										break;
									end
									if (FlatIdent_5ED46 == 0) then
										c = floor((j - 1) / 32) + 1;
										b = (j - 1) % 32;
										FlatIdent_5ED46 = 1;
									end
								end
							end
							masks[i] = a;
						end
						FlatIdent_8199B = 1;
					end
					if (1 == FlatIdent_8199B) then
						return masks, "c";
					end
				end
			else
				local FlatIdent_51F42 = 0;
				while true do
					if (FlatIdent_51F42 == 0) then
						fmask = nil;
						for i = 1, #lists do
							local FlatIdent_E652 = 0;
							local s;
							while true do
								if (FlatIdent_E652 == 1) then
									masks[i] = s;
									break;
								end
								if (0 == FlatIdent_E652) then
									s = {};
									for _, j in ipairs(lists[i]) do
										s[j] = true;
									end
									FlatIdent_E652 = 1;
								end
							end
						end
						FlatIdent_51F42 = 1;
					end
					if (FlatIdent_51F42 == 1) then
						return masks, "s";
					end
				end
			end
			break;
		end
	end
end
local function subset(A, B, mode)
	if (mode == "n") then
		return band(A, B) == A;
	elseif (mode == "c") then
		local FlatIdent_6053C = 0;
		while true do
			if (FlatIdent_6053C == 0) then
				for i = 1, math.max(#A, #B) do
					if (band(A[i] or 0, B[i] or 0) ~= (A[i] or 0)) then
						return false;
					end
				end
				return true;
			end
		end
	else
		for k in pairs(A) do
			if not B[k] then
				return false;
			end
		end
		return true;
	end
end
local function maskDiff(A, B, mode)
	local out = {};
	if (mode == "n") then
		local invA = (bnot and band(bnot(A), fmask or 0)) or nil;
		local d = ((invA ~= nil) and band(B, invA)) or B;
		local i = 0;
		while d ~= 0 do
			if (band(d, 1) ~= 0) then
				if (invA == nil) then
					if (band(A, 2 ^ i) == 0) then
						out[#out + 1] = i + 1;
					end
				else
					out[#out + 1] = i + 1;
				end
			end
			d = rshift(d, 1);
			i = i + 1;
		end
	elseif (mode == "c") then
		for ci = 1, #B do
			local FlatIdent_8F59B = 0;
			local bv;
			local av;
			local na;
			local d;
			local base;
			local k;
			while true do
				if (FlatIdent_8F59B == 1) then
					na = band((bnot and bnot(av)) or (4294967295 - av), 4294967295);
					d = band(bv, na);
					FlatIdent_8F59B = 2;
				end
				if (FlatIdent_8F59B == 0) then
					bv = B[ci] or 0;
					av = A[ci] or 0;
					FlatIdent_8F59B = 1;
				end
				if (FlatIdent_8F59B == 3) then
					while d ~= 0 do
						if (band(d, 1) ~= 0) then
							out[#out + 1] = base + k + 1;
						end
						d = rshift(d, 1);
						k = k + 1;
					end
					break;
				end
				if (FlatIdent_8F59B == 2) then
					base = (ci - 1) * 32;
					k = 0;
					FlatIdent_8F59B = 3;
				end
			end
		end
	else
		for idx in pairs(B) do
			if not A[idx] then
				out[#out + 1] = idx;
			end
		end
	end
	return out;
end
local function choose(n, k)
	local FlatIdent_2D2B8 = 0;
	local r;
	while true do
		if (FlatIdent_2D2B8 == 2) then
			for i = 1, k do
				local FlatIdent_74348 = 0;
				while true do
					if (FlatIdent_74348 == 0) then
						r = r * (n - (k - i));
						r = r / i;
						break;
					end
				end
			end
			return r;
		end
		if (FlatIdent_2D2B8 == 1) then
			if (k > (n - k)) then
				k = n - k;
			end
			r = 1;
			FlatIdent_2D2B8 = 2;
		end
		if (FlatIdent_2D2B8 == 0) then
			if ((k < 0) or (k > n)) then
				return 0;
			end
			if ((k == 0) or (k == n)) then
				return 1;
			end
			FlatIdent_2D2B8 = 1;
		end
	end
end
local ecache = {};
local eorder = {};
local esize = 3000;
local eptr = 1;
local function ecachePut(k, v)
	local FlatIdent_759F1 = 0;
	while true do
		if (0 == FlatIdent_759F1) then
			if not ecache[k] then
				local FlatIdent_324DE = 0;
				local old;
				while true do
					if (FlatIdent_324DE == 1) then
						eorder[eptr] = k;
						eptr = (eptr % esize) + 1;
						break;
					end
					if (0 == FlatIdent_324DE) then
						old = eorder[eptr];
						if old then
							ecache[old] = nil;
						end
						FlatIdent_324DE = 1;
					end
				end
			end
			ecache[k] = v;
			break;
		end
	end
end
local function ecacheGet(k)
	return ecache[k];
end
local function ecacheClear()
	local FlatIdent_7909D = 0;
	while true do
		if (FlatIdent_7909D == 1) then
			eptr = 1;
			break;
		end
		if (FlatIdent_7909D == 0) then
			ecache = {};
			eorder = {};
			FlatIdent_7909D = 1;
		end
	end
end
local function compKey(constraints)
	local FlatIdent_4CC24 = 0;
	local p;
	while true do
		if (FlatIdent_4CC24 == 0) then
			p = {};
			for i = 1, #constraints do
				local c = constraints[i];
				local ix = {table.unpack(c.ix)};
				sort(ix);
				p[#p + 1] = table.concat(ix, ",") .. ":" .. c.r;
			end
			FlatIdent_4CC24 = 1;
		end
		if (FlatIdent_4CC24 == 1) then
			sort(p);
			return table.concat(p, "|");
		end
	end
end
local function enumerate(group, constraints, cap)
	local n = #group;
	local hits = {};
	for i = 1, n do
		hits[i] = 0;
	end
	local total = 0;
	local lo, hi = nil, nil;
	local dist = {};
	local perK = {};
	for i = 1, n do
		perK[i] = {};
	end
	local vc = {};
	for i = 1, n do
		vc[i] = {};
	end
	for ci = 1, #constraints do
		for _, j in ipairs(constraints[ci].ix) do
			vc[j][#vc[j] + 1] = ci;
		end
	end
	local ord = {};
	for i = 1, n do
		ord[i] = i;
	end
	local tgt = {};
	for i = 1, n do
		local m = huge;
		for _, ci in ipairs(vc[i]) do
			local c = constraints[ci];
			local t = min(c.r, #c.ix - c.r);
			if (t < m) then
				m = t;
			end
		end
		tgt[i] = ((#vc[i] > 0) and m) or huge;
	end
	sort(ord, function(a, b)
		local na, nb = #vc[a], #vc[b];
		if (na ~= nb) then
			return na > nb;
		end
		return tgt[a] < tgt[b];
	end);
	local ca = {};
	local cu = {};
	for ci = 1, #constraints do
		local FlatIdent_28F1 = 0;
		while true do
			if (0 == FlatIdent_28F1) then
				ca[ci] = 0;
				cu[ci] = #constraints[ci].ix;
				break;
			end
		end
	end
	local asgn = {};
	for i = 1, n do
		asgn[i] = 0;
	end
	local stop, capped = false, false;
	local function go(d, mines)
		if stop then
			return;
		end
		if (d > n) then
			local FlatIdent_8A742 = 0;
			while true do
				if (0 == FlatIdent_8A742) then
					total = total + 1;
					dist[mines] = (dist[mines] or 0) + 1;
					FlatIdent_8A742 = 1;
				end
				if (FlatIdent_8A742 == 1) then
					if (not lo or (mines < lo)) then
						lo = mines;
					end
					if (not hi or (mines > hi)) then
						hi = mines;
					end
					FlatIdent_8A742 = 2;
				end
				if (FlatIdent_8A742 == 3) then
					return;
				end
				if (FlatIdent_8A742 == 2) then
					for i = 1, n do
						if (asgn[i] == 1) then
							hits[i] = hits[i] + 1;
							local a = perK[i];
							a[mines] = (a[mines] or 0) + 1;
						end
					end
					if (cap and (total >= cap)) then
						local FlatIdent_2E9CB = 0;
						while true do
							if (FlatIdent_2E9CB == 0) then
								stop = true;
								capped = true;
								break;
							end
						end
					end
					FlatIdent_8A742 = 3;
				end
			end
		end
		local v = ord[d];
		local vcs = vc[v];
		local ok0 = true;
		for i = 1, #vcs do
			local FlatIdent_29E69 = 0;
			local ci;
			while true do
				if (FlatIdent_29E69 == 1) then
					if ((ca[ci] > constraints[ci].r) or ((ca[ci] + cu[ci]) < constraints[ci].r)) then
						ok0 = false;
					end
					break;
				end
				if (FlatIdent_29E69 == 0) then
					ci = vcs[i];
					cu[ci] = cu[ci] - 1;
					FlatIdent_29E69 = 1;
				end
			end
		end
		if ok0 then
			local FlatIdent_19F98 = 0;
			while true do
				if (FlatIdent_19F98 == 0) then
					asgn[v] = 0;
					go(d + 1, mines);
					break;
				end
			end
		end
		for i = 1, #vcs do
			cu[vcs[i]] = cu[vcs[i]] + 1;
		end
		if stop then
			return;
		end
		local ok1 = true;
		for i = 1, #vcs do
			local FlatIdent_75224 = 0;
			local ci;
			while true do
				if (FlatIdent_75224 == 0) then
					ci = vcs[i];
					cu[ci] = cu[ci] - 1;
					FlatIdent_75224 = 1;
				end
				if (FlatIdent_75224 == 1) then
					ca[ci] = ca[ci] + 1;
					if ((ca[ci] > constraints[ci].r) or ((ca[ci] + cu[ci]) < constraints[ci].r)) then
						ok1 = false;
					end
					break;
				end
			end
		end
		if ok1 then
			asgn[v] = 1;
			go(d + 1, mines + 1);
		end
		for i = 1, #vcs do
			local FlatIdent_494F6 = 0;
			while true do
				if (FlatIdent_494F6 == 0) then
					cu[vcs[i]] = cu[vcs[i]] + 1;
					ca[vcs[i]] = ca[vcs[i]] - 1;
					break;
				end
			end
		end
		asgn[v] = 0;
	end
	go(1, 0);
	dist[0] = dist[0] or 0;
	for k = 1, n do
		dist[k] = dist[k] or 0;
	end
	return total, hits, lo or 0, hi or 0, dist, perK, capped;
end
local function enumerateCached(group, constraints, cap)
	local FlatIdent_581C8 = 0;
	local keys;
	local k;
	local hit;
	local t;
	local h;
	local lo;
	local hi;
	local d;
	local pk;
	local capped;
	while true do
		if (FlatIdent_581C8 == 0) then
			keys = {};
			for i = 1, #group do
				keys[i] = group[i].k;
			end
			FlatIdent_581C8 = 1;
		end
		if (FlatIdent_581C8 == 4) then
			return t, h, lo, hi, d, pk, false, capped;
		end
		if (FlatIdent_581C8 == 3) then
			t, h, lo, hi, d, pk, capped = enumerate(group, constraints, cap);
			if (t and (t > 0) and not capped) then
				ecachePut(k, {t=t,h=h,lo=lo,hi=hi,d=d,pk=pk});
			end
			FlatIdent_581C8 = 4;
		end
		if (FlatIdent_581C8 == 2) then
			hit = ecacheGet(k);
			if hit then
				return hit.t, hit.h, hit.lo, hit.hi, hit.d, hit.pk, true, false;
			end
			FlatIdent_581C8 = 3;
		end
		if (FlatIdent_581C8 == 1) then
			sort(keys);
			k = compKey(constraints) .. #group .. "|" .. table.concat(keys, ",");
			FlatIdent_581C8 = 2;
		end
	end
end
local tmpQ = {};
local function neighbors(c, kF, kC, out)
	local FlatIdent_4508F = 0;
	local nbs;
	local fc;
	local n;
	while true do
		if (FlatIdent_4508F == 2) then
			for i = n + 1, #out do
				out[i] = nil;
			end
			return n, fc;
		end
		if (FlatIdent_4508F == 1) then
			n = 0;
			for i = 1, #nbs do
				local nb = nbs[i];
				if kF[nb] then
					fc = fc + 1;
				elseif (not kC[nb] and (nb.hidden == true)) then
					local FlatIdent_40070 = 0;
					while true do
						if (FlatIdent_40070 == 0) then
							n = n + 1;
							out[n] = nb;
							break;
						end
					end
				end
			end
			FlatIdent_4508F = 2;
		end
		if (FlatIdent_4508F == 0) then
			nbs = c.neigh;
			fc = 0;
			FlatIdent_4508F = 1;
		end
	end
end
local mA = {};
local mI = {};
local function runPatterns(kF, kC)
	local any = false;
	for pass = 1, 12 do
		local changed = false;
		local meta = {};
		local mlists = {};
		for i = 1, #board.revealed do
			local FlatIdent_81225 = 0;
			local cell;
			local nu;
			local fc;
			local rem;
			while true do
				if (FlatIdent_81225 == 1) then
					rem = (cell.clue or 0) - fc;
					if ((rem >= 0) and (nu > 0)) then
						local FlatIdent_6679B = 0;
						local unks;
						while true do
							if (FlatIdent_6679B == 1) then
								meta[#meta + 1] = {unks=unks,rem=rem};
								mlists[#mlists + 1] = unks;
								break;
							end
							if (FlatIdent_6679B == 0) then
								unks = {};
								for j = 1, nu do
									unks[j] = tmpQ[j];
								end
								FlatIdent_6679B = 1;
							end
						end
					end
					break;
				end
				if (FlatIdent_81225 == 0) then
					cell = board.revealed[i];
					nu, fc = neighbors(cell, kF, kC, tmpQ);
					FlatIdent_81225 = 1;
				end
			end
		end
		if (#meta == 0) then
			break;
		end
		local fi = {};
		local fl = {};
		local idx = 1;
		for i = 1, #mlists do
			for _, c in ipairs(mlists[i]) do
				if not fi[c] then
					fi[c] = idx;
					fl[idx] = c;
					idx = idx + 1;
				end
			end
		end
		local mil = {};
		for i = 1, #meta do
			local FlatIdent_2DA99 = 0;
			local arr;
			while true do
				if (FlatIdent_2DA99 == 1) then
					mil[i] = arr;
					break;
				end
				if (FlatIdent_2DA99 == 0) then
					arr = {};
					for _, c in ipairs(meta[i].unks) do
						arr[#arr + 1] = fi[c];
					end
					FlatIdent_2DA99 = 1;
				end
			end
		end
		local masks, mode = buildMasks(#fl, mil);
		for i = 1, #meta do
			local FlatIdent_912A7 = 0;
			local A;
			local Ai;
			local sa;
			while true do
				if (FlatIdent_912A7 == 0) then
					A = meta[i];
					Ai = masks[i];
					FlatIdent_912A7 = 1;
				end
				if (FlatIdent_912A7 == 1) then
					sa = #A.unks;
					for j = 1, #meta do
						if (i ~= j) then
							local FlatIdent_5724B = 0;
							local B;
							while true do
								if (0 == FlatIdent_5724B) then
									B = meta[j];
									if ((sa <= #B.unks) and subset(Ai, masks[j], mode)) then
										local FlatIdent_8E5B4 = 0;
										local di;
										while true do
											if (FlatIdent_8E5B4 == 0) then
												di = maskDiff(Ai, masks[j], mode);
												if (#di > 0) then
													local FlatIdent_7873D = 0;
													local dm;
													while true do
														if (FlatIdent_7873D == 0) then
															dm = B.rem - A.rem;
															if (dm == 0) then
																for d = 1, #di do
																	local FlatIdent_8638E = 0;
																	local c;
																	while true do
																		if (FlatIdent_8638E == 0) then
																			c = fl[di[d]];
																			if (c and not kC[c]) then
																				local FlatIdent_8FBAE = 0;
																				while true do
																					if (FlatIdent_8FBAE == 0) then
																						kC[c] = true;
																						board.cleared[c] = true;
																						FlatIdent_8FBAE = 1;
																					end
																					if (FlatIdent_8FBAE == 1) then
																						changed = true;
																						break;
																					end
																				end
																			end
																			break;
																		end
																	end
																end
															elseif ((dm == #di) and (dm > 0)) then
																for d = 1, #di do
																	local FlatIdent_71EE8 = 0;
																	local c;
																	while true do
																		if (FlatIdent_71EE8 == 0) then
																			c = fl[di[d]];
																			if (c and not kF[c]) then
																				local FlatIdent_89917 = 0;
																				while true do
																					if (FlatIdent_89917 == 1) then
																						changed = true;
																						break;
																					end
																					if (FlatIdent_89917 == 0) then
																						kF[c] = true;
																						board.flagged[c] = true;
																						FlatIdent_89917 = 1;
																					end
																				end
																			end
																			break;
																		end
																	end
																end
															end
															break;
														end
													end
												end
												break;
											end
										end
									end
									break;
								end
							end
						end
					end
					break;
				end
			end
		end
		for i = 1, #meta - 1 do
			local A = meta[i].unks;
			local rA = meta[i].rem;
			for a = 1, #A do
				mA[A[a]] = true;
			end
			for j = i + 1, #meta do
				local B = meta[j].unks;
				local rB = meta[j].rem;
				local inter, onlyA, onlyB = {}, {}, {};
				for _, c in ipairs(B) do
					if mA[c] then
						inter[#inter + 1] = c;
						mI[c] = true;
					else
						onlyB[#onlyB + 1] = c;
					end
				end
				for _, c in ipairs(A) do
					if not mI[c] then
						onlyA[#onlyA + 1] = c;
					end
				end
				for _, c in ipairs(inter) do
					mI[c] = nil;
				end
				local nI, nA, nB = #inter, #onlyA, #onlyB;
				if ((nI > 0) or (nA > 0) or (nB > 0)) then
					local FlatIdent_F26C = 0;
					local iMin;
					local iMax;
					while true do
						if (FlatIdent_F26C == 1) then
							if (iMin <= iMax) then
								local FlatIdent_31077 = 0;
								local cMax;
								local dMax;
								local cMin;
								local dMin;
								while true do
									if (FlatIdent_31077 == 0) then
										cMax = min(nA, rA - iMin);
										dMax = min(nB, rB - iMin);
										FlatIdent_31077 = 1;
									end
									if (2 == FlatIdent_31077) then
										if ((cMax == 0) and (nA > 0)) then
											for _, c in ipairs(onlyA) do
												if not kC[c] then
													local FlatIdent_7B2D6 = 0;
													while true do
														if (FlatIdent_7B2D6 == 0) then
															kC[c] = true;
															board.cleared[c] = true;
															FlatIdent_7B2D6 = 1;
														end
														if (FlatIdent_7B2D6 == 1) then
															changed = true;
															break;
														end
													end
												end
											end
										elseif ((cMin == nA) and (nA > 0)) then
											for _, c in ipairs(onlyA) do
												if not kF[c] then
													kF[c] = true;
													board.flagged[c] = true;
													changed = true;
												end
											end
										end
										if ((dMax == 0) and (nB > 0)) then
											for _, c in ipairs(onlyB) do
												if not kC[c] then
													local FlatIdent_6DFD9 = 0;
													while true do
														if (FlatIdent_6DFD9 == 1) then
															changed = true;
															break;
														end
														if (FlatIdent_6DFD9 == 0) then
															kC[c] = true;
															board.cleared[c] = true;
															FlatIdent_6DFD9 = 1;
														end
													end
												end
											end
										elseif ((dMin == nB) and (nB > 0)) then
											for _, c in ipairs(onlyB) do
												if not kF[c] then
													local FlatIdent_56F59 = 0;
													while true do
														if (FlatIdent_56F59 == 0) then
															kF[c] = true;
															board.flagged[c] = true;
															FlatIdent_56F59 = 1;
														end
														if (1 == FlatIdent_56F59) then
															changed = true;
															break;
														end
													end
												end
											end
										end
										FlatIdent_31077 = 3;
									end
									if (FlatIdent_31077 == 3) then
										if ((iMax == 0) and (nI > 0)) then
											for _, c in ipairs(inter) do
												if not kC[c] then
													local FlatIdent_71E8F = 0;
													while true do
														if (FlatIdent_71E8F == 1) then
															changed = true;
															break;
														end
														if (FlatIdent_71E8F == 0) then
															kC[c] = true;
															board.cleared[c] = true;
															FlatIdent_71E8F = 1;
														end
													end
												end
											end
										elseif ((iMin == nI) and (nI > 0)) then
											for _, c in ipairs(inter) do
												if not kF[c] then
													local FlatIdent_5AB84 = 0;
													while true do
														if (FlatIdent_5AB84 == 1) then
															changed = true;
															break;
														end
														if (FlatIdent_5AB84 == 0) then
															kF[c] = true;
															board.flagged[c] = true;
															FlatIdent_5AB84 = 1;
														end
													end
												end
											end
										end
										break;
									end
									if (1 == FlatIdent_31077) then
										cMin = max(0, rA - iMax);
										dMin = max(0, rB - iMax);
										FlatIdent_31077 = 2;
									end
								end
							end
							break;
						end
						if (FlatIdent_F26C == 0) then
							iMin = max(0, rA - nA, rB - nB);
							iMax = min(nI, rA, rB);
							FlatIdent_F26C = 1;
						end
					end
				end
			end
			for a = 1, #A do
				mA[A[a]] = nil;
			end
		end
		if not changed then
			break;
		end
		any = true;
	end
	return any;
end
local function runLocalSolver(kF, kC)
	local FlatIdent_5077 = 0;
	local any;
	local maxSz;
	local nd;
	local c2n;
	local nbs2;
	local solved;
	while true do
		if (FlatIdent_5077 == 0) then
			any = false;
			maxSz = 12;
			nd = {};
			for i = 1, #board.revealed do
				local FlatIdent_6E214 = 0;
				local cell;
				local nu;
				local fc;
				local rem;
				while true do
					if (FlatIdent_6E214 == 1) then
						rem = (cell.clue or 0) - fc;
						if ((rem >= 0) and (nu > 0)) then
							local unks = {};
							for j = 1, nu do
								unks[j] = tmpQ[j];
							end
							nd[#nd + 1] = {unks=unks,rem=rem};
						end
						break;
					end
					if (FlatIdent_6E214 == 0) then
						cell = board.revealed[i];
						nu, fc = neighbors(cell, kF, kC, tmpQ);
						FlatIdent_6E214 = 1;
					end
				end
			end
			FlatIdent_5077 = 1;
		end
		if (FlatIdent_5077 == 2) then
			for ci = 1, #nd do
				local FlatIdent_71493 = 0;
				local nb;
				while true do
					if (FlatIdent_71493 == 1) then
						nbs2[ci] = nb;
						break;
					end
					if (FlatIdent_71493 == 0) then
						nb = {};
						for _, c in ipairs(nd[ci].unks) do
							if c2n[c] then
								for _, cj in ipairs(c2n[c]) do
									if (cj ~= ci) then
										nb[cj] = true;
									end
								end
							end
						end
						FlatIdent_71493 = 1;
					end
				end
			end
			solved = {};
			for ci = 1, #nd do
				local FlatIdent_75331 = 0;
				local grp;
				local inG;
				local uSet;
				local uList;
				local cands;
				while true do
					if (FlatIdent_75331 == 2) then
						for _, c in ipairs(nd[ci].unks) do
							local FlatIdent_7D3C9 = 0;
							while true do
								if (0 == FlatIdent_7D3C9) then
									uSet[c] = true;
									uList[#uList + 1] = c;
									break;
								end
							end
						end
						cands = {};
						FlatIdent_75331 = 3;
					end
					if (4 == FlatIdent_75331) then
						for _, nb in ipairs(cands) do
							if not inG[nb] then
								local nc = 0;
								for _, c in ipairs(nd[nb].unks) do
									if not uSet[c] then
										nc = nc + 1;
									end
								end
								if ((#uList + nc) <= maxSz) then
									grp[#grp + 1] = nb;
									inG[nb] = true;
									for _, c in ipairs(nd[nb].unks) do
										if not uSet[c] then
											uSet[c] = true;
											uList[#uList + 1] = c;
										end
									end
									for nb2 in pairs(nbs2[nb]) do
										if not inG[nb2] then
											local FlatIdent_23FF9 = 0;
											local nc2;
											while true do
												if (FlatIdent_23FF9 == 0) then
													nc2 = 0;
													for _, c in ipairs(nd[nb2].unks) do
														if not uSet[c] then
															nc2 = nc2 + 1;
														end
													end
													FlatIdent_23FF9 = 1;
												end
												if (FlatIdent_23FF9 == 1) then
													if ((#uList + nc2) <= maxSz) then
														local FlatIdent_810B1 = 0;
														while true do
															if (FlatIdent_810B1 == 0) then
																grp[#grp + 1] = nb2;
																inG[nb2] = true;
																FlatIdent_810B1 = 1;
															end
															if (FlatIdent_810B1 == 1) then
																for _, c in ipairs(nd[nb2].unks) do
																	if not uSet[c] then
																		local FlatIdent_70003 = 0;
																		while true do
																			if (FlatIdent_70003 == 0) then
																				uSet[c] = true;
																				uList[#uList + 1] = c;
																				break;
																			end
																		end
																	end
																end
																break;
															end
														end
													end
													break;
												end
											end
										end
									end
								end
							end
						end
						if ((#grp >= 2) and (#uList >= 2)) then
							local FlatIdent_322B4 = 0;
							local gk;
							while true do
								if (FlatIdent_322B4 == 1) then
									if not solved[gk] then
										local FlatIdent_2DF14 = 0;
										local lid;
										local cons;
										local t;
										local h;
										local _;
										local capped;
										while true do
											if (FlatIdent_2DF14 == 1) then
												for idx, c in ipairs(uList) do
													lid[c] = idx;
												end
												cons = {};
												FlatIdent_2DF14 = 2;
											end
											if (FlatIdent_2DF14 == 2) then
												for _, gi in ipairs(grp) do
													local FlatIdent_243F3 = 0;
													local cd;
													local ix;
													while true do
														if (FlatIdent_243F3 == 1) then
															for _, c in ipairs(cd.unks) do
																ix[#ix + 1] = lid[c];
															end
															cons[#cons + 1] = {ix=ix,r=cd.rem};
															break;
														end
														if (FlatIdent_243F3 == 0) then
															cd = nd[gi];
															ix = {};
															FlatIdent_243F3 = 1;
														end
													end
												end
												t, h, _, _, _, _, capped = enumerate(uList, cons, 50000);
												FlatIdent_2DF14 = 3;
											end
											if (0 == FlatIdent_2DF14) then
												solved[gk] = true;
												lid = {};
												FlatIdent_2DF14 = 1;
											end
											if (FlatIdent_2DF14 == 3) then
												if (t and (t > 0) and not capped) then
													for idx = 1, #uList do
														local FlatIdent_47EEF = 0;
														local c;
														while true do
															if (FlatIdent_47EEF == 0) then
																c = uList[idx];
																if (h[idx] == 0) then
																	if not kC[c] then
																		local FlatIdent_73F66 = 0;
																		while true do
																			if (FlatIdent_73F66 == 1) then
																				any = true;
																				break;
																			end
																			if (FlatIdent_73F66 == 0) then
																				kC[c] = true;
																				board.cleared[c] = true;
																				FlatIdent_73F66 = 1;
																			end
																		end
																	end
																elseif (h[idx] == t) then
																	if not kF[c] then
																		kF[c] = true;
																		board.flagged[c] = true;
																		any = true;
																	end
																end
																break;
															end
														end
													end
												end
												break;
											end
										end
									end
									break;
								end
								if (FlatIdent_322B4 == 0) then
									sort(grp);
									gk = table.concat(grp, ",");
									FlatIdent_322B4 = 1;
								end
							end
						end
						break;
					end
					if (FlatIdent_75331 == 3) then
						for nb in pairs(nbs2[ci]) do
							cands[#cands + 1] = nb;
						end
						sort(cands, function(a, b)
							local FlatIdent_270C = 0;
							local na;
							local nb;
							while true do
								if (FlatIdent_270C == 0) then
									na, nb = 0, 0;
									for _, c in ipairs(nd[a].unks) do
										if not uSet[c] then
											na = na + 1;
										end
									end
									FlatIdent_270C = 1;
								end
								if (FlatIdent_270C == 1) then
									for _, c in ipairs(nd[b].unks) do
										if not uSet[c] then
											nb = nb + 1;
										end
									end
									return na < nb;
								end
							end
						end);
						FlatIdent_75331 = 4;
					end
					if (FlatIdent_75331 == 1) then
						uSet = {};
						uList = {};
						FlatIdent_75331 = 2;
					end
					if (FlatIdent_75331 == 0) then
						grp = {ci};
						inG = {[ci]=true};
						FlatIdent_75331 = 1;
					end
				end
			end
			return any;
		end
		if (FlatIdent_5077 == 1) then
			if (#nd < 2) then
				return false;
			end
			c2n = {};
			for ci = 1, #nd do
				for _, c in ipairs(nd[ci].unks) do
					local FlatIdent_7AA3 = 0;
					while true do
						if (0 == FlatIdent_7AA3) then
							if not c2n[c] then
								c2n[c] = {};
							end
							c2n[c][#c2n[c] + 1] = ci;
							break;
						end
					end
				end
			end
			nbs2 = {};
			FlatIdent_5077 = 2;
		end
	end
end
local function cluster(list, eps)
	local out = {};
	if (#list == 0) then
		return out;
	end
	local cc, cn = list[1], 1;
	for i = 2, #list do
		local FlatIdent_C79F = 0;
		local v;
		while true do
			if (0 == FlatIdent_C79F) then
				v = list[i];
				if (abs(v - cc) <= eps) then
					local FlatIdent_47A85 = 0;
					while true do
						if (FlatIdent_47A85 == 0) then
							cn = cn + 1;
							cc = cc + ((v - cc) / cn);
							break;
						end
					end
				else
					out[#out + 1] = cc;
					cc = v;
					cn = 1;
				end
				break;
			end
		end
	end
	out[#out + 1] = cc;
	return out;
end
local function mid(t)
	local FlatIdent_1EAB2 = 0;
	while true do
		if (0 == FlatIdent_1EAB2) then
			if (#t == 0) then
				return nil;
			end
			sort(t);
			FlatIdent_1EAB2 = 1;
		end
		if (1 == FlatIdent_1EAB2) then
			return t[floor((#t + 1) / 2)];
		end
	end
end
local function spacing(centers)
	local FlatIdent_1B418 = 0;
	local d;
	while true do
		if (FlatIdent_1B418 == 0) then
			if (#centers < 2) then
				return 4;
			end
			d = {};
			FlatIdent_1B418 = 1;
		end
		if (FlatIdent_1B418 == 1) then
			for i = 2, #centers do
				d[#d + 1] = abs(centers[i] - centers[i - 1]);
			end
			return mid(d) or 4;
		end
	end
end
local function nearest(v, centers)
	local FlatIdent_1F138 = 0;
	local n;
	local lo;
	local hi;
	local bi;
	local bd;
	while true do
		if (FlatIdent_1F138 == 2) then
			bi, bd = 1, huge;
			for _, i in ipairs({(lo - 1),lo,(lo + 1)}) do
				if ((i >= 1) and (i <= n)) then
					local FlatIdent_2E3CE = 0;
					local d;
					while true do
						if (FlatIdent_2E3CE == 0) then
							d = abs(v - centers[i]);
							if (d < bd) then
								local FlatIdent_FC26 = 0;
								while true do
									if (FlatIdent_FC26 == 0) then
										bd = d;
										bi = i;
										break;
									end
								end
							end
							break;
						end
					end
				end
			end
			FlatIdent_1F138 = 3;
		end
		if (FlatIdent_1F138 == 0) then
			n = #centers;
			if (n == 0) then
				return -1;
			end
			FlatIdent_1F138 = 1;
		end
		if (FlatIdent_1F138 == 1) then
			lo, hi = 1, n;
			while lo <= hi do
				local FlatIdent_8BF78 = 0;
				local m;
				local cm;
				while true do
					if (FlatIdent_8BF78 == 1) then
						if (cm == v) then
							return m - 1;
						end
						if (cm < v) then
							lo = m + 1;
						else
							hi = m - 1;
						end
						break;
					end
					if (0 == FlatIdent_8BF78) then
						m = floor((lo + hi) / 2);
						cm = centers[m];
						FlatIdent_8BF78 = 1;
					end
				end
			end
			FlatIdent_1F138 = 2;
		end
		if (FlatIdent_1F138 == 3) then
			return bi - 1;
		end
	end
end
local function buildGrid()
	local FlatIdent_98E39 = 0;
	local root;
	local folder;
	local parts;
	local raw;
	local sy;
	local sc;
	local px;
	local pz;
	local ex;
	local ez;
	local py;
	while true do
		if (3 == FlatIdent_98E39) then
			raw = {};
			sy, sc = 0, 0;
			for _, p in pairs(parts) do
				local pos = p and p.Position;
				if pos then
					local FlatIdent_3C8BC = 0;
					while true do
						if (1 == FlatIdent_3C8BC) then
							sc = sc + 1;
							break;
						end
						if (FlatIdent_3C8BC == 0) then
							raw[#raw + 1] = {p=p,pos=pos};
							sy = sy + pos.Y;
							FlatIdent_3C8BC = 1;
						end
					end
				end
			end
			FlatIdent_98E39 = 4;
		end
		if (2 == FlatIdent_98E39) then
			folder = root:FindFirstChild("Parts");
			if not folder then
				return false;
			end
			parts = folder:GetChildren();
			FlatIdent_98E39 = 3;
		end
		if (FlatIdent_98E39 == 5) then
			sort(pz);
			ex = spacing(px) * 0.6;
			ez = spacing(pz) * 0.6;
			FlatIdent_98E39 = 6;
		end
		if (FlatIdent_98E39 == 1) then
			board.flat = {};
			root = workspace:FindFirstChild("Flag");
			if not root then
				return false;
			end
			FlatIdent_98E39 = 2;
		end
		if (6 == FlatIdent_98E39) then
			state.cx = cluster(px, ex);
			state.cz = cluster(pz, ez);
			cols = #state.cx;
			FlatIdent_98E39 = 7;
		end
		if (FlatIdent_98E39 == 4) then
			px, pz = {}, {};
			for i = 1, #raw do
				px[#px + 1] = raw[i].pos.X;
				pz[#pz + 1] = raw[i].pos.Z;
			end
			sort(px);
			FlatIdent_98E39 = 5;
		end
		if (FlatIdent_98E39 == 7) then
			rows = #state.cz;
			py = ((sc > 0) and (sy / sc)) or 0;
			for iz = 0, rows - 1 do
				for ix = 0, cols - 1 do
					local FlatIdent_13951 = 0;
					local row;
					local cell;
					while true do
						if (FlatIdent_13951 == 1) then
							cell = {ix=ix,iz=iz,part=nil,pos=Vector3.new(state.cx[ix + 1] or 0, py, state.cz[iz + 1] or 0),kind="unknown",clue=nil,k=toKey(ix, iz),hidden=true,neigh=nil,_sig=-1};
							board.cells[cell.k] = cell;
							FlatIdent_13951 = 2;
						end
						if (FlatIdent_13951 == 0) then
							row = board.rows[ix];
							if not row then
								local FlatIdent_458D1 = 0;
								while true do
									if (FlatIdent_458D1 == 0) then
										row = {};
										board.rows[ix] = row;
										break;
									end
								end
							end
							FlatIdent_13951 = 1;
						end
						if (FlatIdent_13951 == 2) then
							row[iz] = cell;
							board.flat[#board.flat + 1] = cell;
							break;
						end
					end
				end
			end
			FlatIdent_98E39 = 8;
		end
		if (FlatIdent_98E39 == 8) then
			for i = 1, #raw do
				local FlatIdent_21387 = 0;
				local p;
				local pos;
				local ix;
				local iz;
				while true do
					if (FlatIdent_21387 == 2) then
						if ((ix >= 0) and (ix < cols) and (iz >= 0) and (iz < rows)) then
							local cell = board.rows[ix][iz];
							if (cell and not cell.part) then
								local FlatIdent_397D1 = 0;
								while true do
									if (FlatIdent_397D1 == 0) then
										cell.part = p;
										cell.pos = pos;
										break;
									end
								end
							end
						end
						break;
					end
					if (FlatIdent_21387 == 1) then
						ix = nearest(pos.X, state.cx);
						iz = nearest(pos.Z, state.cz);
						FlatIdent_21387 = 2;
					end
					if (FlatIdent_21387 == 0) then
						p = raw[i].p;
						pos = raw[i].pos;
						FlatIdent_21387 = 1;
					end
				end
			end
			for iz = 0, rows - 1 do
				for ix = 0, cols - 1 do
					local FlatIdent_6B92D = 0;
					local c;
					local nb;
					while true do
						if (FlatIdent_6B92D == 1) then
							for dz = -1, 1 do
								for dx = -1, 1 do
									if not ((dx == 0) and (dz == 0)) then
										local jx, jz = ix + dx, iz + dz;
										if ((jx >= 0) and (jx < cols) and (jz >= 0) and (jz < rows)) then
											nb[#nb + 1] = board.rows[jx][jz];
										end
									end
								end
							end
							c.neigh = nb;
							break;
						end
						if (FlatIdent_6B92D == 0) then
							c = board.rows[ix][iz];
							nb = {};
							FlatIdent_6B92D = 1;
						end
					end
				end
			end
			return true;
		end
		if (0 == FlatIdent_98E39) then
			board.cells = {};
			board.revealed = {};
			board.rows = {};
			FlatIdent_98E39 = 1;
		end
	end
end
local function gridReady()
	local FlatIdent_95359 = 0;
	while true do
		if (0 == FlatIdent_95359) then
			if (state.cx and state.cz and (cols > 0) and (rows > 0) and board.rows and (next(board.cells) ~= nil)) then
				return true;
			end
			return buildGrid();
		end
	end
end
local function readBoard()
	board.revealed = {};
	local changed = false;
	local flat = board.flat;
	for i = 1, #flat do
		local FlatIdent_8384B = 0;
		local cell;
		local part;
		while true do
			if (FlatIdent_8384B == 0) then
				cell = flat[i];
				part = cell.part;
				FlatIdent_8384B = 1;
			end
			if (FlatIdent_8384B == 1) then
				if part then
					cell.kind = "unknown";
					cell.hidden = true;
					cell.clue = nil;
					local gui = part:FindFirstChild("NumberGui");
					if gui then
						local tl = gui:FindFirstChild("TextLabel");
						local v = tl and (tl.Text or tl.Value);
						local s = (v and string.match(tostring(v), "^%s*(.-)%s*$")) or "";
						if ((s ~= "") and isNum(s)) then
							local n = tonumber(s);
							if (n and (n >= 1) and (n <= 8)) then
								cell.clue = n;
							end
						end
						cell.hidden = false;
					end
					if (cell.clue and not cell.hidden) then
						local FlatIdent_68E5B = 0;
						while true do
							if (FlatIdent_68E5B == 0) then
								cell.kind = "clue";
								board.revealed[#board.revealed + 1] = cell;
								break;
							end
						end
					end
					local sig = ((cell.hidden and 1) or 0) + ((cell.clue or 0) * 4);
					if (sig ~= (cell._sig or -1)) then
						local FlatIdent_70C30 = 0;
						while true do
							if (FlatIdent_70C30 == 0) then
								cell._sig = sig;
								changed = true;
								break;
							end
						end
					end
				end
				break;
			end
		end
	end
	if changed then
		state.tick = (state.tick or 0) + 1;
	end
end
local function propagate(kF, kC)
	local FlatIdent_6719E = 0;
	local q;
	local qh;
	local inQ;
	local any;
	while true do
		if (FlatIdent_6719E == 1) then
			for i = 1, #board.revealed do
				local c = board.revealed[i];
				q[#q + 1] = c;
				inQ[c] = true;
			end
			any = false;
			FlatIdent_6719E = 2;
		end
		if (FlatIdent_6719E == 2) then
			while qh <= #q do
				local FlatIdent_28E8A = 0;
				local cell;
				local nu;
				local fc;
				while true do
					if (1 == FlatIdent_28E8A) then
						inQ[cell] = nil;
						nu, fc = neighbors(cell, kF, kC, tmpQ);
						FlatIdent_28E8A = 2;
					end
					if (FlatIdent_28E8A == 2) then
						if (nu > 0) then
							local FlatIdent_6BDA4 = 0;
							local rem;
							while true do
								if (FlatIdent_6BDA4 == 0) then
									rem = (cell.clue or 0) - fc;
									if (rem == 0) then
										for u = 1, nu do
											local FlatIdent_5C97A = 0;
											local c;
											while true do
												if (FlatIdent_5C97A == 0) then
													c = tmpQ[u];
													if not kC[c] then
														local FlatIdent_4EC26 = 0;
														while true do
															if (FlatIdent_4EC26 == 1) then
																any = true;
																for _, nb in ipairs(c.neigh) do
																	if ((nb.kind == "clue") and not inQ[nb]) then
																		inQ[nb] = true;
																		q[#q + 1] = nb;
																	end
																end
																break;
															end
															if (FlatIdent_4EC26 == 0) then
																kC[c] = true;
																board.cleared[c] = true;
																FlatIdent_4EC26 = 1;
															end
														end
													end
													break;
												end
											end
										end
									elseif ((rem == nu) and (rem > 0)) then
										for u = 1, nu do
											local FlatIdent_7268B = 0;
											local c;
											while true do
												if (FlatIdent_7268B == 0) then
													c = tmpQ[u];
													if not kF[c] then
														local FlatIdent_2F8E7 = 0;
														while true do
															if (FlatIdent_2F8E7 == 1) then
																any = true;
																for _, nb in ipairs(c.neigh) do
																	if ((nb.kind == "clue") and not inQ[nb]) then
																		local FlatIdent_D6BD = 0;
																		while true do
																			if (FlatIdent_D6BD == 0) then
																				inQ[nb] = true;
																				q[#q + 1] = nb;
																				break;
																			end
																		end
																	end
																end
																break;
															end
															if (FlatIdent_2F8E7 == 0) then
																kF[c] = true;
																board.flagged[c] = true;
																FlatIdent_2F8E7 = 1;
															end
														end
													end
													break;
												end
											end
										end
									end
									break;
								end
							end
						end
						break;
					end
					if (FlatIdent_28E8A == 0) then
						cell = q[qh];
						qh = qh + 1;
						FlatIdent_28E8A = 1;
					end
				end
			end
			return any;
		end
		if (FlatIdent_6719E == 0) then
			q, qh = {}, 1;
			inQ = {};
			FlatIdent_6719E = 1;
		end
	end
end
local function solve()
	if (not state.cx or not state.cz or (cols == 0) or (rows == 0)) then
		return;
	end
	if (#board.revealed == 0) then
		local FlatIdent_4609C = 0;
		while true do
			if (FlatIdent_4609C == 0) then
				board.flagged = {};
				board.cleared = {};
				FlatIdent_4609C = 1;
			end
			if (FlatIdent_4609C == 1) then
				board.probs = {};
				return;
			end
		end
	end
	board.flagged = {};
	board.cleared = {};
	board.probs = {};
	local kF = {};
	local kC = {};
	propagate(kF, kC);
	if USE_PATTERNS then
		if runPatterns(kF, kC) then
			propagate(kF, kC);
		end
	end
	if (not next(board.flagged) and not next(board.cleared)) then
		if runLocalSolver(kF, kC) then
			propagate(kF, kC);
		end
	end
	local fset = {};
	local flist = {};
	for i = 1, #board.revealed do
		local cell = board.revealed[i];
		local nu = neighbors(cell, kF, kC, tmpQ);
		for u = 1, nu do
			local FlatIdent_28DC7 = 0;
			local c;
			while true do
				if (FlatIdent_28DC7 == 0) then
					c = tmpQ[u];
					if not fset[c] then
						fset[c] = true;
						flist[#flist + 1] = c;
					end
					break;
				end
			end
		end
	end
	local idOf = {};
	for i = 1, #flist do
		idOf[flist[i]] = i;
	end
	local cons = {};
	for i = 1, #board.revealed do
		local FlatIdent_97F0B = 0;
		local cell;
		local nu;
		local fc;
		local rem;
		while true do
			if (FlatIdent_97F0B == 0) then
				cell = board.revealed[i];
				nu, fc = neighbors(cell, kF, kC, tmpQ);
				FlatIdent_97F0B = 1;
			end
			if (FlatIdent_97F0B == 1) then
				rem = (cell.clue or 0) - fc;
				if ((rem >= 0) and (nu > 0)) then
					local FlatIdent_63284 = 0;
					local ix;
					while true do
						if (FlatIdent_63284 == 1) then
							if (#ix > 0) then
								cons[#cons + 1] = {ix=ix,r=rem};
							end
							break;
						end
						if (FlatIdent_63284 == 0) then
							ix = {};
							for u = 1, nu do
								ix[#ix + 1] = idOf[tmpQ[u]];
							end
							FlatIdent_63284 = 1;
						end
					end
				end
				break;
			end
		end
	end
	local par, rnk = {}, {};
	for i = 1, #flist do
		local FlatIdent_643B6 = 0;
		while true do
			if (FlatIdent_643B6 == 0) then
				par[i] = i;
				rnk[i] = 0;
				break;
			end
		end
	end
	local function fp(x)
		local FlatIdent_8DBF2 = 0;
		while true do
			if (FlatIdent_8DBF2 == 0) then
				while par[x] ~= x do
					local FlatIdent_4BEE8 = 0;
					while true do
						if (FlatIdent_4BEE8 == 0) then
							par[x] = par[par[x]];
							x = par[x];
							break;
						end
					end
				end
				return x;
			end
		end
	end
	local function fu(a, b)
		local ra, rb = fp(a), fp(b);
		if (ra == rb) then
			return;
		end
		if (rnk[ra] < rnk[rb]) then
			par[ra] = rb;
		elseif (rnk[ra] > rnk[rb]) then
			par[rb] = ra;
		else
			par[rb] = ra;
			rnk[ra] = rnk[ra] + 1;
		end
	end
	for _, c in ipairs(cons) do
		local FlatIdent_91AA8 = 0;
		local first;
		while true do
			if (FlatIdent_91AA8 == 0) then
				first = c.ix[1];
				for j = 2, #c.ix do
					fu(first, c.ix[j]);
				end
				break;
			end
		end
	end
	local byRoot = {};
	for i = 1, #flist do
		local FlatIdent_6873F = 0;
		local r;
		local g;
		while true do
			if (FlatIdent_6873F == 1) then
				if not g then
					g = {};
					byRoot[r] = g;
				end
				g[#g + 1] = i;
				break;
			end
			if (FlatIdent_6873F == 0) then
				r = fp(i);
				g = byRoot[r];
				FlatIdent_6873F = 1;
			end
		end
	end
	local comps = {};
	for _, g in pairs(byRoot) do
		comps[#comps + 1] = g;
	end
	local cdata = {};
	for ci = 1, #comps do
		local comp = comps[ci];
		local sz = #comp;
		local grp = {};
		for i = 1, sz do
			grp[i] = flist[comp[i]];
		end
		local cm = {};
		for i = 1, sz do
			cm[comp[i]] = i;
		end
		local lc = {};
		for _, c in ipairs(cons) do
			local FlatIdent_1351F = 0;
			local li;
			while true do
				if (1 == FlatIdent_1351F) then
					if (#li > 0) then
						lc[#lc + 1] = {ix=li,r=c.r};
					end
					break;
				end
				if (0 == FlatIdent_1351F) then
					li = {};
					for _, j in ipairs(c.ix) do
						local FlatIdent_32079 = 0;
						local l;
						while true do
							if (0 == FlatIdent_32079) then
								l = cm[j];
								if l then
									li[#li + 1] = l;
								end
								break;
							end
						end
					end
					FlatIdent_1351F = 1;
				end
			end
		end
		local agg = (sz <= (MAX_COMP_SIZE + 6)) and (#lc <= (MAX_COMP_SIZE + 8));
		if (((sz <= MAX_COMP_SIZE) or agg) and (#lc > 0)) then
			local FlatIdent_24300 = 0;
			local t;
			local h;
			local lo;
			local hi;
			local d;
			local pk;
			local _;
			local capped;
			while true do
				if (0 == FlatIdent_24300) then
					t, h, lo, hi, d, pk, _, capped = enumerateCached(grp, lc, SOLUTION_LIMIT);
					if (t and (t > 0) and not capped) then
						local FlatIdent_8FACF = 0;
						while true do
							if (0 == FlatIdent_8FACF) then
								cdata[#cdata + 1] = {grp=grp,lo=lo,hi=hi,t=t,d=d,pk=pk};
								for i = 1, #grp do
									board.probs[grp[i]] = h[i] / t;
								end
								break;
							end
						end
					else
						cdata[#cdata + 1] = {grp=grp,lo=0,hi=sz,t=0};
					end
					break;
				end
			end
		else
			cdata[#cdata + 1] = {grp=grp,lo=0,hi=sz,t=0};
		end
	end
	local allEnum = true;
	for i = 1, #cdata do
		if not cdata[i].d then
			allEnum = false;
			break;
		end
	end
	if (allEnum and (MINE_COUNT > 0)) then
		local fc = 0;
		for _ in pairs(kF) do
			fc = fc + 1;
		end
		local rem = math.max(0, MINE_COUNT - fc);
		local outside = 0;
		for _, c in pairs(board.cells) do
			if ((c.hidden == true) and not fset[c] and not kF[c] and not kC[c]) then
				outside = outside + 1;
			end
		end
		local co = {};
		for t = 0, outside do
			co[t] = choose(outside, t);
		end
		local dp = {[0]=1};
		for i = 1, #cdata do
			local FlatIdent_52478 = 0;
			local ci;
			local ndp;
			while true do
				if (FlatIdent_52478 == 0) then
					ci = cdata[i];
					ndp = {};
					FlatIdent_52478 = 1;
				end
				if (1 == FlatIdent_52478) then
					for kp, wp in pairs(dp) do
						for kt = 0, #ci.d do
							local FlatIdent_7FA00 = 0;
							local wt;
							while true do
								if (FlatIdent_7FA00 == 0) then
									wt = ci.d[kt] or 0;
									if (wt > 0) then
										ndp[kp + kt] = (ndp[kp + kt] or 0) + (wp * wt);
									end
									break;
								end
							end
						end
					end
					dp = ndp;
					break;
				end
			end
		end
		local totalW = 0;
		for x, w in pairs(dp) do
			local FlatIdent_447EB = 0;
			local t;
			while true do
				if (FlatIdent_447EB == 0) then
					t = rem - x;
					if ((t >= 0) and (t <= outside)) then
						totalW = totalW + (w * (co[t] or 0));
					end
					break;
				end
			end
		end
		if (totalW > 0) then
			local pre = {};
			pre[0] = {[0]=1};
			for i = 1, #cdata do
				local FlatIdent_60A2E = 0;
				local prev;
				local cur;
				local ci;
				while true do
					if (FlatIdent_60A2E == 2) then
						pre[i] = cur;
						break;
					end
					if (FlatIdent_60A2E == 0) then
						prev = pre[i - 1];
						cur = {};
						FlatIdent_60A2E = 1;
					end
					if (FlatIdent_60A2E == 1) then
						ci = cdata[i];
						for kp, wp in pairs(prev) do
							for kt = 0, #ci.d do
								local FlatIdent_8ECD7 = 0;
								local wt;
								while true do
									if (FlatIdent_8ECD7 == 0) then
										wt = ci.d[kt] or 0;
										if (wt > 0) then
											cur[kp + kt] = (cur[kp + kt] or 0) + (wp * wt);
										end
										break;
									end
								end
							end
						end
						FlatIdent_60A2E = 2;
					end
				end
			end
			local suf = {};
			suf[#cdata + 1] = {[0]=1};
			for i = #cdata, 1, -1 do
				local nxt = suf[i + 1];
				local cur = {};
				local ci = cdata[i];
				for kn, wn in pairs(nxt) do
					for kt = 0, #ci.d do
						local FlatIdent_2CC55 = 0;
						local wt;
						while true do
							if (FlatIdent_2CC55 == 0) then
								wt = ci.d[kt] or 0;
								if (wt > 0) then
									cur[kn + kt] = (cur[kn + kt] or 0) + (wn * wt);
								end
								break;
							end
						end
					end
				end
				suf[i] = cur;
			end
			for i = 1, #cdata do
				local ci = cdata[i];
				if (ci.d and ci.pk and ci.t and (ci.t > 0)) then
					local FlatIdent_771FD = 0;
					local dO;
					local G;
					while true do
						if (FlatIdent_771FD == 0) then
							dO = {};
							for ka, wa in pairs(pre[i - 1]) do
								for kb, wb in pairs(suf[i + 1]) do
									dO[ka + kb] = (dO[ka + kb] or 0) + (wa * wb);
								end
							end
							FlatIdent_771FD = 1;
						end
						if (1 == FlatIdent_771FD) then
							G = {};
							for kt = 0, #ci.d do
								local s = 0;
								for ko, wo in pairs(dO) do
									local t = rem - (kt + ko);
									if ((t >= 0) and (t <= outside)) then
										s = s + (wo * (co[t] or 0));
									end
								end
								G[kt] = s;
							end
							FlatIdent_771FD = 2;
						end
						if (2 == FlatIdent_771FD) then
							for j = 1, #ci.grp do
								local FlatIdent_65365 = 0;
								local pk;
								local num;
								local p;
								while true do
									if (FlatIdent_65365 == 1) then
										for kt, w in pairs(pk) do
											num = num + (w * (G[kt] or 0));
										end
										p = num / totalW;
										FlatIdent_65365 = 2;
									end
									if (FlatIdent_65365 == 2) then
										board.probs[ci.grp[j]] = p;
										if (p <= 1e-12) then
											if not kC[ci.grp[j]] then
												local FlatIdent_32B1C = 0;
												while true do
													if (FlatIdent_32B1C == 0) then
														kC[ci.grp[j]] = true;
														board.cleared[ci.grp[j]] = true;
														break;
													end
												end
											end
										elseif ((1 - p) <= 1e-12) then
											if not kF[ci.grp[j]] then
												local FlatIdent_8E53E = 0;
												while true do
													if (FlatIdent_8E53E == 0) then
														kF[ci.grp[j]] = true;
														board.flagged[ci.grp[j]] = true;
														break;
													end
												end
											end
										end
										break;
									end
									if (FlatIdent_65365 == 0) then
										pk = ci.pk[j];
										num = 0;
										FlatIdent_65365 = 1;
									end
								end
							end
							break;
						end
					end
				end
			end
		end
	end
	local acc = {};
	for i = 1, #board.revealed do
		local cell = board.revealed[i];
		local nu, fc = neighbors(cell, kF, kC, tmpQ);
		local rem = (cell.clue or 0) - fc;
		if ((rem > 0) and (nu > 0)) then
			local FlatIdent_885BC = 0;
			local pe;
			local tg;
			while true do
				if (FlatIdent_885BC == 0) then
					pe = rem / nu;
					tg = 1 - (min(rem, nu - rem) / max(nu, 1));
					FlatIdent_885BC = 1;
				end
				if (FlatIdent_885BC == 1) then
					for u = 1, nu do
						local c = tmpQ[u];
						if (not kF[c] and not kC[c]) then
							local FlatIdent_4C119 = 0;
							local e;
							while true do
								if (FlatIdent_4C119 == 1) then
									e.n = e.n + 1;
									e.p[e.n] = pe;
									FlatIdent_4C119 = 2;
								end
								if (FlatIdent_4C119 == 0) then
									e = acc[c];
									if not e then
										local FlatIdent_4B539 = 0;
										while true do
											if (FlatIdent_4B539 == 0) then
												e = {n=0,p={},t={},ps=1};
												acc[c] = e;
												break;
											end
										end
									end
									FlatIdent_4C119 = 1;
								end
								if (FlatIdent_4C119 == 2) then
									e.t[e.n] = tg;
									e.ps = e.ps * (1 - pe);
									break;
								end
							end
						end
					end
					break;
				end
			end
		end
	end
	for cell, e in pairs(acc) do
		if (not kF[cell] and not kC[cell] and not board.probs[cell]) then
			if (e.n == 1) then
				board.probs[cell] = e.p[1];
			else
				local pno = 1 - e.ps;
				local ws, ts = 0, 0;
				for i = 1, e.n do
					local FlatIdent_2C3E6 = 0;
					local w;
					while true do
						if (FlatIdent_2C3E6 == 1) then
							ts = ts + w;
							break;
						end
						if (FlatIdent_2C3E6 == 0) then
							w = e.t[i] + 0.1;
							ws = ws + (e.p[i] * w);
							FlatIdent_2C3E6 = 1;
						end
					end
				end
				local pw = ws / ts;
				local p;
				if ((pno >= 0.5) and (pw >= 0.5)) then
					p = max(pno, pw);
				elseif ((pno <= 0.5) and (pw <= 0.5)) then
					p = min(pno, pw);
				else
					p = pw;
				end
				board.probs[cell] = p;
			end
		end
	end
	for c in pairs(board.flagged) do
		local FlatIdent_21811 = 0;
		while true do
			if (FlatIdent_21811 == 0) then
				board.cleared[c] = nil;
				board.probs[c] = nil;
				break;
			end
		end
	end
	for c in pairs(board.cleared) do
		local FlatIdent_13AEB = 0;
		while true do
			if (FlatIdent_13AEB == 0) then
				board.flagged[c] = nil;
				board.probs[c] = nil;
				break;
			end
		end
	end
end
local function hashParts(parts)
	local n = #parts;
	if (n == 0) then
		return "0";
	end
	local step = math.max(1, floor(n / 12));
	local a = {tostring(n)};
	local k = 1;
	for i = 1, n, step do
		local p = parts[i];
		local pos = p and p.Position;
		if pos then
			a[#a + 1] = tostring(floor((pos.X * 10) + 0.5)) .. "," .. tostring(floor((pos.Z * 10) + 0.5));
		end
		k = k + 1;
		if (k > 12) then
			break;
		end
	end
	return table.concat(a, "|");
end
local function needsRebuild()
	local FlatIdent_398FF = 0;
	local root;
	local folder;
	local parts;
	local n;
	local h;
	while true do
		if (0 == FlatIdent_398FF) then
			root = workspace:FindFirstChild("Flag");
			if not root then
				return true;
			end
			folder = root:FindFirstChild("Parts");
			if not folder then
				return true;
			end
			FlatIdent_398FF = 1;
		end
		if (FlatIdent_398FF == 2) then
			if (state.partCount ~= n) then
				local FlatIdent_5D1D5 = 0;
				while true do
					if (FlatIdent_5D1D5 == 1) then
						return true;
					end
					if (FlatIdent_5D1D5 == 0) then
						state.partCount = n;
						state.partHash = h;
						FlatIdent_5D1D5 = 1;
					end
				end
			end
			if (state.partHash ~= h) then
				local FlatIdent_2B908 = 0;
				while true do
					if (FlatIdent_2B908 == 0) then
						state.partHash = h;
						return true;
					end
				end
			end
			return false;
		end
		if (FlatIdent_398FF == 1) then
			parts = folder:GetChildren();
			n = #parts;
			h = hashParts(parts);
			if (state.folder ~= folder) then
				local FlatIdent_18172 = 0;
				while true do
					if (FlatIdent_18172 == 0) then
						state.folder = folder;
						state.partCount = n;
						FlatIdent_18172 = 1;
					end
					if (FlatIdent_18172 == 1) then
						state.partHash = h;
						return true;
					end
				end
			end
			FlatIdent_398FF = 2;
		end
	end
end
local function fullReset()
	local FlatIdent_80A55 = 0;
	while true do
		if (FlatIdent_80A55 == 0) then
			state.cx = nil;
			state.cz = nil;
			cols = 0;
			FlatIdent_80A55 = 1;
		end
		if (FlatIdent_80A55 == 2) then
			board.rows = {};
			board.flat = {};
			state.tick = 0;
			FlatIdent_80A55 = 3;
		end
		if (FlatIdent_80A55 == 1) then
			rows = 0;
			board.cells = {};
			board.revealed = {};
			FlatIdent_80A55 = 2;
		end
		if (3 == FlatIdent_80A55) then
			state.lastTick = -1;
			ecacheClear();
			break;
		end
	end
end
local pool = {};
local poolN = 0;
local poolUsed = 0;
local function getLabel()
	local FlatIdent_39FCB = 0;
	local d;
	while true do
		if (FlatIdent_39FCB == 2) then
			pool[poolN] = d;
			return d;
		end
		if (FlatIdent_39FCB == 0) then
			poolUsed = poolUsed + 1;
			if (poolUsed <= poolN) then
				local FlatIdent_661EB = 0;
				local d;
				while true do
					if (FlatIdent_661EB == 1) then
						return d;
					end
					if (FlatIdent_661EB == 0) then
						d = pool[poolUsed];
						d.Visible = true;
						FlatIdent_661EB = 1;
					end
				end
			end
			FlatIdent_39FCB = 1;
		end
		if (FlatIdent_39FCB == 1) then
			d = Drawing.new("Text", {Size=13,Center=true,Outline=true,OutlineColor=BLACK,Color=RED,Visible=false});
			poolN = poolN + 1;
			FlatIdent_39FCB = 2;
		end
	end
end
local function hideExtra()
	for i = poolUsed + 1, poolN do
		pool[i].Visible = false;
	end
end
local function project(cell)
	local pos = (cell.part and cell.part.Position) or cell.pos;
	if not pos then
		return nil, nil;
	end
	local sc, on = pos:WorldToScreen();
	if not on then
		return nil, nil;
	end
	return floor(sc.X + 0.5), floor(sc.Y + 0.5);
end
local function pct(p)
	return string.format("%d%%", floor(((floor((p * 20) + 0.5) / 20) * 100) + 0.5));
end
local function draw()
	poolUsed = 0;
	for cell in pairs(board.cleared or {}) do
		if not board.flagged[cell] then
			local sx, sy = project(cell);
			if (sx and sy) then
				local FlatIdent_30046 = 0;
				local d;
				local d2;
				while true do
					if (FlatIdent_30046 == 1) then
						d.Color = MINT;
						d.Size = 15;
						FlatIdent_30046 = 2;
					end
					if (FlatIdent_30046 == 3) then
						d2.Text = "clr";
						d2.Color = MINT_DIM;
						FlatIdent_30046 = 4;
					end
					if (FlatIdent_30046 == 2) then
						d.Position = Vector2.new(sx, sy - 6);
						d2 = getLabel();
						FlatIdent_30046 = 3;
					end
					if (FlatIdent_30046 == 0) then
						d = getLabel();
						d.Text = "S";
						FlatIdent_30046 = 1;
					end
					if (FlatIdent_30046 == 4) then
						d2.Size = 10;
						d2.Position = Vector2.new(sx, sy + 8);
						break;
					end
				end
			end
		end
	end
	for cell, p in pairs(board.probs or {}) do
		if (not board.flagged[cell] and not board.cleared[cell]) then
			local sx, sy = project(cell);
			if (sx and sy) then
				if (p >= MINE_THRESHOLD) then
					local FlatIdent_12809 = 0;
					local d;
					local d2;
					while true do
						if (1 == FlatIdent_12809) then
							d.Color = HOT_RED;
							d.Size = 14;
							FlatIdent_12809 = 2;
						end
						if (FlatIdent_12809 == 2) then
							d.Position = Vector2.new(sx, sy - 6);
							d2 = getLabel();
							FlatIdent_12809 = 3;
						end
						if (3 == FlatIdent_12809) then
							d2.Text = "mine?";
							d2.Color = HOT_RED2;
							FlatIdent_12809 = 4;
						end
						if (FlatIdent_12809 == 4) then
							d2.Size = 10;
							d2.Position = Vector2.new(sx, sy + 8);
							break;
						end
						if (FlatIdent_12809 == 0) then
							d = getLabel();
							d.Text = pct(p);
							FlatIdent_12809 = 1;
						end
					end
				elseif (p <= SAFE_THRESHOLD) then
					local FlatIdent_5C5DB = 0;
					local d;
					local d2;
					while true do
						if (FlatIdent_5C5DB == 4) then
							d2.Size = 10;
							d2.Position = Vector2.new(sx, sy + 8);
							break;
						end
						if (FlatIdent_5C5DB == 2) then
							d.Position = Vector2.new(sx, sy - 6);
							d2 = getLabel();
							FlatIdent_5C5DB = 3;
						end
						if (FlatIdent_5C5DB == 1) then
							d.Color = SKY;
							d.Size = 14;
							FlatIdent_5C5DB = 2;
						end
						if (FlatIdent_5C5DB == 0) then
							d = getLabel();
							d.Text = pct(1 - p);
							FlatIdent_5C5DB = 1;
						end
						if (FlatIdent_5C5DB == 3) then
							d2.Text = "safe?";
							d2.Color = SKY_DIM;
							FlatIdent_5C5DB = 4;
						end
					end
				else
					local FlatIdent_45054 = 0;
					local d;
					local d2;
					while true do
						if (FlatIdent_45054 == 2) then
							d.Position = Vector2.new(sx, sy - 6);
							d2 = getLabel();
							FlatIdent_45054 = 3;
						end
						if (FlatIdent_45054 == 1) then
							d.Color = AMBER;
							d.Size = 14;
							FlatIdent_45054 = 2;
						end
						if (FlatIdent_45054 == 4) then
							d2.Size = 10;
							d2.Position = Vector2.new(sx, sy + 8);
							break;
						end
						if (FlatIdent_45054 == 3) then
							d2.Text = "idk";
							d2.Color = AMBER_DIM;
							FlatIdent_45054 = 4;
						end
						if (FlatIdent_45054 == 0) then
							d = getLabel();
							d.Text = pct(p);
							FlatIdent_45054 = 1;
						end
					end
				end
			end
		end
	end
	for cell in pairs(board.flagged or {}) do
		local FlatIdent_40B3B = 0;
		local sx;
		local sy;
		while true do
			if (FlatIdent_40B3B == 0) then
				sx, sy = project(cell);
				if (sx and sy) then
					local FlatIdent_88AD8 = 0;
					local d;
					local d2;
					while true do
						if (FlatIdent_88AD8 == 3) then
							d2.Text = "!!!";
							d2.Color = RED_DIM;
							FlatIdent_88AD8 = 4;
						end
						if (FlatIdent_88AD8 == 4) then
							d2.Size = 11;
							d2.Position = Vector2.new(sx, sy + 8);
							break;
						end
						if (FlatIdent_88AD8 == 0) then
							d = getLabel();
							d.Text = "M";
							FlatIdent_88AD8 = 1;
						end
						if (2 == FlatIdent_88AD8) then
							d.Position = Vector2.new(sx, sy - 6);
							d2 = getLabel();
							FlatIdent_88AD8 = 3;
						end
						if (1 == FlatIdent_88AD8) then
							d.Color = RED;
							d.Size = 15;
							FlatIdent_88AD8 = 2;
						end
					end
				end
				break;
			end
		end
	end
	hideExtra();
end
local frame = 0;
task.spawn(function()
	local FlatIdent_2A75 = 0;
	local solveNext;
	while true do
		if (FlatIdent_2A75 == 0) then
			solveNext = false;
			while true do
				local FlatIdent_7B4B6 = 0;
				local ok;
				local err;
				while true do
					if (FlatIdent_7B4B6 == 1) then
						if not ok then
							print("[solver] error: " .. tostring(err));
						end
						task.wait(0);
						break;
					end
					if (FlatIdent_7B4B6 == 0) then
						frame = frame + 1;
						ok, err = pcall(function()
							local FlatIdent_4D046 = 0;
							while true do
								if (FlatIdent_4D046 == 0) then
									if needsRebuild() then
										fullReset();
									end
									if gridReady() then
										local FlatIdent_3AA8C = 0;
										while true do
											if (FlatIdent_3AA8C == 0) then
												readBoard();
												if (state.tick ~= state.lastTick) then
													local FlatIdent_951F1 = 0;
													while true do
														if (FlatIdent_951F1 == 0) then
															state.lastTick = state.tick;
															solve();
															FlatIdent_951F1 = 1;
														end
														if (FlatIdent_951F1 == 1) then
															solveNext = true;
															break;
														end
													end
												elseif solveNext then
													local FlatIdent_14BE1 = 0;
													while true do
														if (FlatIdent_14BE1 == 0) then
															solveNext = false;
															solve();
															break;
														end
													end
												end
												break;
											end
										end
									end
									FlatIdent_4D046 = 1;
								end
								if (FlatIdent_4D046 == 1) then
									draw();
									break;
								end
							end
						end);
						FlatIdent_7B4B6 = 1;
					end
				end
			end
			break;
		end
	end
end);
print("[solver] ready.");
