var reader;
var progress = document.querySelector('.percent');
var vertices = [];
var triangles = [];
var rawVertices = [];
var rawTriangles = [];
var modules = '';
var calls = '';
var functions = '';
var vertexIndex = 0;
var converted = 0;
var totalObjects = 0;
var fileName = '';

function _reset() {
  vertices = [];
  triangles = [];
  rawVertices = [];
  rawTriangles = [];
  modules = '';
  calls = '';
  functions = '';
  vertexIndex = 0;
  converted = 0;
  totalObjects = 0;
  document.getElementById('error').innerText = '';
  document.getElementById('conversion').innerText = '';
  document.getElementById("download").style.display = "none"
}

function simplifyMesh(verts, tris, gridSize) {
  if (tris.length < 100 || gridSize <= 0) {
    return {vertices: verts, triangles: tris};
  }

  var min = [Infinity, Infinity, Infinity];
  var max = [-Infinity, -Infinity, -Infinity];
  for (var i = 0; i < verts.length; i++) {
    var v = verts[i];
    if (v[0] < min[0]) min[0] = v[0];
    if (v[1] < min[1]) min[1] = v[1];
    if (v[2] < min[2]) min[2] = v[2];
    if (v[0] > max[0]) max[0] = v[0];
    if (v[1] > max[1]) max[1] = v[1];
    if (v[2] > max[2]) max[2] = v[2];
  }

  var cellSize = [
    (max[0] - min[0]) / gridSize || 1,
    (max[1] - min[1]) / gridSize || 1,
    (max[2] - min[2]) / gridSize || 1
  ];

  var cellData = {};
  for (var i = 0; i < verts.length; i++) {
    var v = verts[i];
    var cx = Math.floor((v[0] - min[0]) / cellSize[0]);
    var cy = Math.floor((v[1] - min[1]) / cellSize[1]);
    var cz = Math.floor((v[2] - min[2]) / cellSize[2]);
    var key = cx + ',' + cy + ',' + cz;
    if (!cellData[key]) {
      cellData[key] = {sx: 0, sy: 0, sz: 0, count: 0};
    }
    cellData[key].sx += v[0];
    cellData[key].sy += v[1];
    cellData[key].sz += v[2];
    cellData[key].count++;
  }

  var newVerts = [];
  var cellToIdx = {};
  for (var key in cellData) {
    var cell = cellData[key];
    var cx = cell.sx / cell.count;
    var cy = cell.sy / cell.count;
    var cz = cell.sz / cell.count;
    // round to 5 decimal places for consistency
    var rx = Math.round(cx * 1e5) / 1e5;
    var ry = Math.round(cy * 1e5) / 1e5;
    var rz = Math.round(cz * 1e5) / 1e5;
    cellToIdx[key] = newVerts.length;
    newVerts.push([rx, ry, rz]);
  }

  var oldToNew = [];
  for (var i = 0; i < verts.length; i++) {
    var v = verts[i];
    var cx = Math.floor((v[0] - min[0]) / cellSize[0]);
    var cy = Math.floor((v[1] - min[1]) / cellSize[1]);
    var cz = Math.floor((v[2] - min[2]) / cellSize[2]);
    oldToNew.push(cellToIdx[cx + ',' + cy + ',' + cz]);
  }

  var newTris = [];
  for (var i = 0; i < tris.length; i++) {
    var t = tris[i];
    var n0 = oldToNew[t[0]];
    var n1 = oldToNew[t[1]];
    var n2 = oldToNew[t[2]];
    if (n0 !== n1 && n1 !== n2 && n0 !== n2) {
      newTris.push([n0, n1, n2]);
    }
  }

  return {vertices: newVerts, triangles: newTris};
}

function buildStrings(verts, tris) {
  vertices = [];
  triangles = [];
  for (var i = 0; i < verts.length; i++) {
    var v = verts[i];
    vertices.push('[' + v[0] + ',' + v[1] + ',' + v[2] + ']');
  }
  for (var i = 0; i < tris.length; i++) {
    var t = tris[i];
    triangles.push('[' + t[0] + ',' + t[1] + ',' + t[2] + ']');
  }
}

function closeMesh(verts, tris) {
  var edgeMap = {};
  for (var i = 0; i < tris.length; i++) {
    var t = tris[i];
    for (var j = 0; j < 3; j++) {
      var a = t[j];
      var b = t[(j + 1) % 3];
      var key = a < b ? a + ',' + b : b + ',' + a;
      if (!edgeMap[key]) edgeMap[key] = {count: 0, tris: []};
      edgeMap[key].count++;
      edgeMap[key].tris.push({tri: i, a: a, b: b});
    }
  }

  var boundaryEdges = [];
  for (var key in edgeMap) {
    if (edgeMap[key].count === 1) {
      var parts = key.split(',');
      var a = parseInt(parts[0]);
      var b = parseInt(parts[1]);
      boundaryEdges.push({a: a, b: b});
    }
  }

  if (boundaryEdges.length === 0) {
    return {vertices: verts, triangles: tris};
  }

  var adj = {};
  for (var i = 0; i < boundaryEdges.length; i++) {
    var e = boundaryEdges[i];
    if (!adj[e.a]) adj[e.a] = [];
    if (!adj[e.b]) adj[e.b] = [];
    adj[e.a].push({edgeIdx: i, other: e.b});
    adj[e.b].push({edgeIdx: i, other: e.a});
  }

  var visited = {};
  var loops = [];

  for (var i = 0; i < boundaryEdges.length; i++) {
    if (visited[i]) continue;

    var loop = [];
    var current = boundaryEdges[i].a;
    var start = current;
    var prevEdge = -1;
    var deadEnd = false;

    while (true) {
      loop.push(current);
      var neighbors = adj[current];
      var nextEdge = -1;
      var next = -1;

      for (var n = 0; n < neighbors.length; n++) {
        if (neighbors[n].edgeIdx === prevEdge) continue;
        if (visited[neighbors[n].edgeIdx]) continue;
        nextEdge = neighbors[n].edgeIdx;
        next = neighbors[n].other;
        break;
      }

      if (nextEdge === -1 || next === -1) {
        deadEnd = true;
        break;
      }
      if (next === start) {
        loop.push(next);
        break;
      }

      visited[nextEdge] = true;
      prevEdge = nextEdge;
      current = next;
    }

    if (!deadEnd && loop.length >= 4) {
      loops.push(loop);
    }
  }

  if (loops.length === 0) return {vertices: verts, triangles: tris};

  function pointInTriangle2D(px, py, ax, ay, bx, by, cx, cy) {
    var d1 = (bx - ax) * (py - ay) - (by - ay) * (px - ax);
    var d2 = (cx - bx) * (py - by) - (cy - by) * (px - bx);
    var d3 = (ax - cx) * (py - cy) - (ay - cy) * (px - cx);
    var hasNeg = (d1 < 0) || (d2 < 0) || (d3 < 0);
    var hasPos = (d1 > 0) || (d2 > 0) || (d3 > 0);
    return !(hasNeg && hasPos);
  }

  var newTris = [];
  for (var l = 0; l < loops.length; l++) {
    var loop = loops[l];
    var n = loop.length - 1;

    var nx = 0, ny = 0, nz = 0;
    for (var i = 0; i < n; i++) {
      var a = verts[loop[i]];
      var b = verts[loop[(i + 1) % n]];
      nx += (a[1] - b[1]) * (a[2] + b[2]);
      ny += (a[2] - b[2]) * (a[0] + b[0]);
      nz += (a[0] - b[0]) * (a[1] + b[1]);
    }
    var len = Math.sqrt(nx * nx + ny * ny + nz * nz);
    if (len < 1e-10) continue;
    nx /= len; ny /= len; nz /= len;

    var absNx = nx < 0 ? -nx : nx;
    var absNy = ny < 0 ? -ny : ny;
    var absNz = nz < 0 ? -nz : nz;
    var projAxis = absNx >= absNy && absNx >= absNz ? 0 :
                  absNy >= absNz ? 1 : 2;

    var p2d = [];
    for (var i = 0; i < n; i++) {
      var v = verts[loop[i]];
      if (projAxis === 0) p2d.push([v[1], v[2]]);
      else if (projAxis === 1) p2d.push([v[0], v[2]]);
      else p2d.push([v[0], v[1]]);
    }

    var signedArea = 0;
    for (var i = 0; i < n; i++) {
      var a2 = p2d[i];
      var b2 = p2d[(i + 1) % n];
      signedArea += a2[0] * b2[1] - b2[0] * a2[1];
    }
    if (signedArea < 0) {
      p2d.reverse();
      var rev = [];
      for (var i = loop.length - 1; i >= 0; i--) rev.push(loop[i]);
      loop = rev;
    }

    var indices = [];
    for (var i = 0; i < n; i++) indices.push(i);

    while (indices.length > 3) {
      var earFound = false;
      for (var i = 0; i < indices.length; i++) {
        var prev = indices[(i - 1 + indices.length) % indices.length];
        var curr = indices[i];
        var next = indices[(i + 1) % indices.length];

        var p0 = p2d[prev], p1 = p2d[curr], p2 = p2d[next];
        var cross = (p1[0] - p0[0]) * (p2[1] - p1[1]) - (p1[1] - p0[1]) * (p2[0] - p1[0]);
        if (cross <= 0) continue;

        var isEar = true;
        for (var j = 0; j < indices.length; j++) {
          if (j === prev || j === curr || j === next) continue;
          var pt = p2d[indices[j]];
          if (pointInTriangle2D(pt[0], pt[1], p0[0], p0[1], p1[0], p1[1], p2[0], p2[1])) {
            isEar = false;
            break;
          }
        }

        if (isEar) {
          newTris.push([loop[prev], loop[curr], loop[next]]);
          indices.splice(i, 1);
          earFound = true;
          break;
        }
      }
      if (!earFound) break;
    }

    if (indices.length === 3) {
      newTris.push([loop[indices[0]], loop[indices[1]], loop[indices[2]]]);
    }
  }

  return {vertices: verts, triangles: tris.concat(newTris)};
}

function parseResult(stl) {
  _reset();
  var isAscii = true;
  for (var i = 0; i < stl.length; i++) {
    if (stl[i].charCodeAt(0) == 0) {
      isAscii = false;
      break;
    }
  }
  if (!isAscii) {
    parseBinaryResult(stl);
  } else {
    parseAsciiResult(stl);
  }
}

function parseBinaryResult(stl) {
  var invertFaces = document.getElementById('flip-surface').checked;
  var br = new BinaryReader(stl);
  br.seek(80);
  var totalTriangles = br.readUInt32();

  var minx = Number.MAX_VALUE;
  var miny = Number.MAX_VALUE;
  var minz = Number.MAX_VALUE;
  var maxx = Number.MIN_VALUE;
  var maxy = Number.MIN_VALUE;
  var maxz = Number.MIN_VALUE;

  var vertexMap = {};

  function addVertex(x, y, z) {
    var rx = Math.round(x * 1e5) / 1e5;
    var ry = Math.round(y * 1e5) / 1e5;
    var rz = Math.round(z * 1e5) / 1e5;
    var key = rx + ',' + ry + ',' + rz;
    if (vertexMap.hasOwnProperty(key)) {
      return vertexMap[key];
    }
    var idx = vertexIndex++;
    vertexMap[key] = idx;
    rawVertices.push([rx, ry, rz]);
    vertices.push('[' + rx + ',' + ry + ',' + rz + ']');
    return idx;
  }

  for (var tr = 0; tr < totalTriangles; tr++) {
    try {
      document.getElementById('conversion').innerText = 'In Progress - Converted ' + (++converted) + ' out of ' + totalTriangles + ' triangles!';
      br.readFloat(); br.readFloat(); br.readFloat();

      var x1 = br.readFloat(), y1 = br.readFloat(), z1 = br.readFloat();
      var x2 = br.readFloat(), y2 = br.readFloat(), z2 = br.readFloat();
      var x3 = br.readFloat(), y3 = br.readFloat(), z3 = br.readFloat();

      minx = Math.min(minx, x1, x2, x3);
      maxx = Math.max(maxx, x1, x2, x3);
      miny = Math.min(miny, y1, y2, y3);
      maxy = Math.max(maxy, y1, y2, y3);
      minz = Math.min(minz, z1, z2, z3);
      maxz = Math.max(maxz, z1, z2, z3);

      br.readUInt16();

      var i1, i2, i3;
      if (!invertFaces) {
        i1 = addVertex(x1, y1, z1);
        i2 = addVertex(x2, y2, z2);
        i3 = addVertex(x3, y3, z3);
      } else {
        i1 = addVertex(x1, y1, z1);
        i2 = addVertex(x3, y3, z3);
        i3 = addVertex(x2, y2, z2);
      }
      rawTriangles.push([i1, i2, i3]);
      triangles.push('[' + i1 + ',' + i2 + ',' + i3 + ']');
    } catch (err) {
      error(err);
      return;
    }
  }

  var boundsMin = `[${minx.toFixed(3)}, ${miny.toFixed(3)}, ${minz.toFixed(3)}]`;
  var boundsMax = `[${maxx.toFixed(3)}, ${maxy.toFixed(3)}, ${maxz.toFixed(3)}]`;

  var simplifyEnabled = document.getElementById('enable-simplify').checked;
  var closeEnabled = document.getElementById('close-mesh').checked;

  var v = rawVertices;
  var t = rawTriangles;

  if (simplifyEnabled) {
    var level = parseInt(document.getElementById('simplify-level').value);
    var gridSize = Math.max(1, Math.round(level / 100 * 200));
    var simplified = simplifyMesh(v, t, gridSize);
    v = simplified.vertices;
    t = simplified.triangles;
  }

  if (closeEnabled) {
    var closed = closeMesh(v, t);
    v = closed.vertices;
    t = closed.triangles;
  }

  buildStrings(v, t);
  saveResult(vertices, triangles, boundsMin, boundsMax);
}

function parseAsciiResult(stl) {
  var invertFaces = document.getElementById('flip-surface').checked;
  var objects = stl.split('endsolid');

  var vertexMap = {};

  function addVertex(x, y, z) {
    var rx = Math.round(x * 1e5) / 1e5;
    var ry = Math.round(y * 1e5) / 1e5;
    var rz = Math.round(z * 1e5) / 1e5;
    var key = rx + ',' + ry + ',' + rz;
    if (vertexMap.hasOwnProperty(key)) {
      return vertexMap[key];
    }
    var idx = vertexIndex++;
    vertexMap[key] = idx;
    rawVertices.push([rx, ry, rz]);
    vertices.push('[' + rx + ',' + ry + ',' + rz + ']');
    return idx;
  }

  for (var o = 0; o < objects.length; o++) {
    var patt = /\bloop[\s\S]*?\endloop/mgi;
    var converted = 0;
    var match = objects[o].match(patt);
    if (match == null) continue;

    var minx = Number.MAX_VALUE;
    var miny = Number.MAX_VALUE;
    var minz = Number.MAX_VALUE;
    var maxx = Number.MIN_VALUE;
    var maxy = Number.MIN_VALUE;
    var maxz = Number.MIN_VALUE;

    for (var i = 0; i < match.length; i++) {
      try {
        document.getElementById('conversion').innerText = 'In Progress - Object ' + (o + 1) + ' out of ' + objects.length + ' Converted ' + (++converted) + ' out of ' + match.length + ' facets!';

        var vpatt = /\bvertex\s+(-?\d+\.?\d*\E?\e?\-?\+?\d*\.?\d*)\s+(-?\d+\.?\d*\E?\e?\-?\+?\d*\.?\d*)\s+(-?\d+\.?\d*\E?\e?\-?\+?\d*\.?\d*)\s*vertex\s+(-?\d+\.?\d*\E?\e?\-?\+?\d*\.?\d*)\s+(-?\d+\.?\d*\E?\e?\-?\+?\d*\.?\d*)\s+(-?\d+\.?\d*\E?\e?\-?\+?\d*\.?\d*)\s*vertex\s+(-?\d+\.?\d*\E?\e?\-?\+?\d*\.?\d*)\s+(-?\d+\.?\d*\E?\e?\-?\+?\d*\.?\d*)\s+(-?\d+\.?\d*\E?\e?\-?\+?\d*\.?\d*)\s*/mgi;

        var v = vpatt.exec(match[i]);
        if (v == null) continue;

        if (v.length != 10) {
          document.getElementById('error').innerText = '\r\nFailed to parse ' + match[i];
          break;
        }

        var a1, a2, a3;
        a1 = parseFloat(v[1]);
        a2 = parseFloat(v[4]);
        a3 = parseFloat(v[7]);
        minx = Math.min(minx, a1, a2, a3);
        maxx = Math.max(maxx, a1, a2, a3);

        a1 = parseFloat(v[2]);
        a2 = parseFloat(v[5]);
        a3 = parseFloat(v[8]);
        miny = Math.min(miny, a1, a2, a3);
        maxy = Math.max(maxy, a1, a2, a3);

        a1 = parseFloat(v[3]);
        a2 = parseFloat(v[6]);
        a3 = parseFloat(v[9]);
        minz = Math.min(minz, a1, a2, a3);
        maxz = Math.max(maxz, a1, a2, a3);

        var i1, i2, i3;
        if (!invertFaces) {
          i1 = addVertex(parseFloat(v[1]), parseFloat(v[2]), parseFloat(v[3]));
          i2 = addVertex(parseFloat(v[4]), parseFloat(v[5]), parseFloat(v[6]));
          i3 = addVertex(parseFloat(v[7]), parseFloat(v[8]), parseFloat(v[9]));
        } else {
          i1 = addVertex(parseFloat(v[1]), parseFloat(v[2]), parseFloat(v[3]));
          i2 = addVertex(parseFloat(v[7]), parseFloat(v[8]), parseFloat(v[9]));
          i3 = addVertex(parseFloat(v[4]), parseFloat(v[5]), parseFloat(v[6]));
        }
        rawTriangles.push([i1, i2, i3]);
        triangles.push('[' + i1 + ',' + i2 + ',' + i3 + ']');
      } catch (err) {
        error(err);
        return;
      }
    }

    var boundsMin = `[${minx.toFixed(3)}, ${miny.toFixed(3)}, ${minz.toFixed(3)}]`;
    var boundsMax = `[${maxx.toFixed(3)}, ${maxy.toFixed(3)}, ${maxz.toFixed(3)}]`;

    var simplifyEnabled = document.getElementById('enable-simplify').checked;
    var closeEnabled = document.getElementById('close-mesh').checked;

    var v = rawVertices;
    var t = rawTriangles;

    if (simplifyEnabled) {
      var level = parseInt(document.getElementById('simplify-level').value);
      var gridSize = Math.max(1, Math.round(level / 100 * 200));
      var simplified = simplifyMesh(v, t, gridSize);
      v = simplified.vertices;
      t = simplified.triangles;
    }

    if (closeEnabled) {
      var closed = closeMesh(v, t);
      v = closed.vertices;
      t = closed.triangles;
    }

    buildStrings(v, t);
    saveResult(vertices, triangles, boundsMin, boundsMax);
  }
}

function error(err) {
  document.getElementById('error').innerText = "An Error has occured while trying to convert your file!\r\nPlease make sure this is a valid STL file.";
  document.getElementById('conversion').innerText = '';
  document.getElementById("download").style.display = "none";
}

function saveResult(vertices, triangles, boundsMin, boundsMax) {
  var verticesString = vertices.join(',');
  var trianglesString = triangles.join(',');

  var poly = 'polyhedron(convexity=10,points=[' + verticesString + '],faces=[' + trianglesString + ']);';

  var objectName = `object${++totalObjects}`;
  var functionMin = `${objectName}Min()`;
  var functionMax = `${objectName}Max()`;

  functions = functions + `function ${functionMin} = ${boundsMin};\r\n`;
  functions = functions + `function ${functionMax} = ${boundsMax};\r\n\r\n`;

  modules = modules + 'module object' + totalObjects + '(scale) {';
  modules = modules + poly + '}\r\n\r\n';
  
  calls = calls + objectName + '(1);\r\n\r\n';

  var result = modules + functions + calls;

  window.URL = window.URL || window.webkitURL;
  var blob = new Blob([result], {
    type: 'text/plain'
  });

  $("#download").attr("href", window.URL.createObjectURL(blob));
  $("#download").attr("download", fileName + ".scad");

  document.getElementById("conversion").innerText = "Conversion complete. Click the button below to download your OpenSCAD file!";
  document.getElementById("triangles").innerText = "Total Triangles: " + triangles.length;
  document.getElementById("bounds").innerText = "Bounds: " + boundsMin + ", " + boundsMax;
  document.getElementById("download").style.display = "";
}

function errorHandler(evt) {
  switch (evt.target.error.code) {
    case evt.target.error.NOT_FOUND_ERR:
      alert('File Not Found!');
      break;
    case evt.target.error.NOT_READABLE_ERR:
      alert('File is not readable');
      break;
    case evt.target.error.ABORT_ERR:
      break;
    default:
      alert('An error occurred reading this file.');
  };
}

function updateProgress(evt) {
  if (evt.lengthComputable) {
    var percentLoaded = Math.round((evt.loaded / evt.total) * 100);
    if (percentLoaded < 100) {
      progress.style.width = percentLoaded + '%';
      progress.textContent = percentLoaded + '%';
    }
  }
}

function handleFileSelect(evt) {
  progress.style.width = '0%';
  progress.textContent = '0%';
  
  var nextFileName = evt.target.files[0].name;
  var extension = String(nextFileName.match(/\.[0-9a-z]+$/i));
  if (extension.toLowerCase() == ".stl") {
    reader = new FileReader();
    reader.onerror = errorHandler;
    reader.onprogress = updateProgress;
    reader.onabort = function(e) {
      alert('File read cancelled');
    };
    reader.onloadstart = function(e) {
      document.getElementById('progress_bar').className = 'loading';
    };

    reader.onload = function(e) {
      progress.style.width = '100%';
      progress.textContent = '100%';
      setTimeout("document.getElementById('progress_bar').className='';", 2000);
      fileName = nextFileName.slice(0, -4);
      document.getElementById('fileName').textContent = " " + fileName + ".scad";    
      parseResult(reader.result);
    }

    reader.readAsBinaryString(evt.target.files[0]);
  } else {
    error();
  }
}

function abortRead() {
  reader.abort();
}

document.getElementById("upload").addEventListener('change', handleFileSelect, false);
