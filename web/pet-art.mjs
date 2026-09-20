// Original shaded pixel portraits: one map cell = one pixel; transparent surround.
import { palette } from './pixel-art.mjs';
const portraits = {
mouse: `
..#####........#####..
.#glllg#......#glllg#.
#glmmmlg#....#glmmmlg#
#lmmssml#....#lmmssml#
#lmmssml######lmmssml#
.#gmmmg#llwwll#gmmmg#.
..####glwwwwllg####..
....#glwwwwwwllgs#...
...#glwwwwwwwwllgs#..
...#lw##wwww##wlgs#..
...#lw#wgwwg#wllgs#..
...#lggggwwgggglgs#..
.###lwwwg##gwwwll###.
....#lwww##wwwlls#...
.####llwwggwwlls####.
.....##llwwlls##.....
.......######.......`,
rabbit: `
.....###....###.....
....#lwl#..#lwl#....
....#lml#..#lml#....
....#lml#..#lml#....
....#lml#..#lml#....
....#lml#..#lml#....
....#lwl####lwl#....
...#llwwwwwwllgs#...
..#llwwwwwwwwllgs#..
..#lw##wwww##wlgs#..
..#lw#wgwwg#wllgs#..
..#lgggwwwwggglgs#..
..#llwwwgmgwwwlgs#..
...#llwww#wwwlgs#...
....#llw#w#wlls#....
.....##lwwwls##.....
.......######.......`,
cat: `
..##............##..
..#l#..........#l#..
..#lm#........#ml#..
..#lmm########mml#..
..#lmglwwwwllgmml#..
..#ggllwggwllgggs#..
.#gllwwgwwgwwllggs#.
.#llwwwwwwwwwwllgs#.
.#lw###wwww###wlgs#.
.#lw#w#gwwg#w#wlls#.
.#lggggwwwwgggglgs#.
###llwwwwwwwwllgs###
..#llwwwg##gwwlls#..
###llwwww##wwllgs###
...#llww#ww#wlls#...
....##llwwwwls##....
......########......`,
dog: `
....############....
..##gmllwwwwllmg##..
.#gmgllwwwwwwllgmg#.
#gmmgllwwwwwwllgmmg#
#gmmslw###ww###lmmg#
#gmmssw#w#ww#w#lmmg#
#gmmsslgggwwggglmmg#
#gmmsslwwwwwwwllmmg#
.#mmsglwww##wwllsm#.
..###glww####wll###.
....#glwww##wwlls#..
....#gllww##wwlgs#..
.....#glw#ml#wls#...
......#glwmlwls#....
.......#glllls#.....
........######......`,
lion: `
......########......
...###gmgmmgmg###...
..#glgmlgmmglgmlg#..
.#gmlgllwwwwllgmlg#.
#gmlgllwwwwwwllgmlg#
#lmgllwwwwwwwwllgmg#
#gmgllw##ww##wllgmg#
#lmglww#wgg#wlllgmg#
#gmglwgggwwgggllgmg#
#lmglwwwg##gwwwlgmg#
#gmgllww####wwllgmg#
.#mggllww##wwllggm#.
.#gmlgll#ww#llgmlg#.
..#gmlgllwwllgmlg#..
...##gmlgggglmg##...
.....##gmmgmg##.....
.......######.......`,
whale: `
............#...#...........
...........#w#.#w#..........
............#w#w#...........
.............#w#...........
.............#g#...........
..........########.........
.......###llwwwwll###......
......#llwwwwwwwwllgg#.....
.....#llwwwwwwwwwwwllgs#...
.##..#lwwwwwwwwwwwwllggs#..
#lg###lwwwwwwww##wwllggs#..
#llggglwwwwwwww#wgwwllgs#..
.#llgglwwwwwwwwggwwllggs#..
..#ggglwwwwwwwwwwwllggss#..
...##ggllllllllllllggss#...
.....#gllllllllllllgss#....
......##wwwwwwwwwwgs##.....
........############.......`
};
export function petMarkup() {
  const symbols = Object.entries(portraits).map(([name, map]) => {
    const rows = map.trim().split('\n');
    const x0 = Math.floor((32-Math.max(...rows.map(r=>r.length)))/2);
    const y0 = Math.floor((32-rows.length)/2);
    const paths = Object.entries(palette).map(([ink, shade]) => {
      let d='';
      rows.forEach((row,y)=>[...row].forEach((p,x)=>{if(p===ink)d+=`M${x0+x} ${y0+y}h1v1h-1z`;}));
      return `<path fill="rgb(${shade},${shade},${shade})" d="${d}"/>`;
    }).join('');
    return `<symbol id="pet-${name}" viewBox="0 0 32 32">${paths}</symbol>`;
  });
  return `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 32 32" width="32" height="32" shape-rendering="crispEdges">\n${symbols.join('\n')}\n</svg>\n`;
}
