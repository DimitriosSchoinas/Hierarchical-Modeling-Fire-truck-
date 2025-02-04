import { lookAt, ortho, mat4, vec3, flatten, normalMatrix, vec4 } from '../../libs/MV.js';
import { loadShadersFromURLS, buildProgramFromSources, setupWebGL } from '../../libs/utils.js';
import { modelView, loadMatrix, multRotationX, multRotationY, multRotationZ, multScale, multTranslation, popMatrix, pushMatrix } from '../../libs/stack.js';

import * as CUBE from '../../libs/objects/cube.js';
import * as SPHERE from '../../libs/objects/sphere.js';
import * as CYLINDER from '../../libs/objects/cylinder.js';
import * as PYRAMID from '../../libs/objects/pyramid.js';
import * as TORUS from '../../libs/objects/torus.js';

const DIST = 10; // Distância da câmera em relação ao objeto principal para criar diferentes vistas (frente, lado, topo, etc.)
const LADDER_SEGMENTS = 8; // Número de degraus das escadas 
const CABIN_x = 4; // Largura (comprimento no eixo x) da cabine 
const CABIN_y = 5; // Altura da cabine no eixo y
const CABIN_Z = 5; // Profundidade da cabine  no eixo z
const LOAD_AREA_x = 9; // Largura da área de carga (parte traseira) 
const LOAD_AREA_y = 4.5; // Altura da área de carga 
const LOAD_AREA_z = 4.5; // Profundidade da área de carga 
const LOWER_BASE_y = 1.5; // Altura da base inferior do camião(estrutura abaixo da cabine e da área de carga)
const WHEEL_RADIUS = 0.8; // Raio das rodas 
const WHEEL_WIDTH = 0.2; // Largura das rodas 
const windowHight = 2; // Altura das janelas da cabine
const windowThickness = 0.1; // Espessura das janelas da cabine
const windowLength = 4.5; // Comprimento das janelas da cabine
const orangePlatformRadius = 3; // Raio da plataforma laranja que segura a escada
const orangePlatformHight = 1; // Altura da plataforma laranja que segura a escada
const floorLength = 25; // Tamanho total do chão com o padrão de xadrez
const blinkerSize = 0.3; // Tamanho das luzes indicadoras (pisca-pisca) do caminhão
const baseTranslationY = 2.5; // Translação no eixo Y para posicionar a base do camião
const whiteBaseTranslationY = -1; // Translação no eixo Y para posicionar as peças brancas abaixo da cabine e área de carga
const wheelsPartTranslationY = -1.5; // Translação no eixo Y para posicionar a parte das rodas
const frontWheelsX = -3; // Posição X das rodas dianteiras
const backWheelsX = 5; // Posição X das rodas traseiras
const WheelsZ = 2.3; // Posição Z das rodas (distância em relação ao eixo central do camião)
const widnowTranslationY = 0.5; // Translação no eixo Y para posicionar as janelas da cabine
const ladderSegmentScale = [0.25, 0.25, 2]; // Escala de cada degrau da escada, nos eixos x, y e z, respectivamente
const ladderSupportScale = [10, 0.5, 0.5]; // Escala das partes laterais de suporte da escada, nos eixos x, y e z
const frontLightsScale = 0.5; // Escala dos faróis dianteiros do caminhão (raio)
const blackColor = [0, 0, 0, 1]; // Cor preta (RGBA) usada para desenhar partes do camião
const greyColor = [0.9, 0.9, 0.9, 1]; // Cor cinza claro (RGBA) usada para desenhar partes do camião
const whiteColor = [1, 1, 1, 1]; // Cor branca (RGBA) usada para desenhar partes do camião
const redColor = [1, 0, 0, 1]; // Cor vermelha (RGBA) usada para desenhar a cabine e a área de carga do camião
const orangeColor = [1, 0.4, 0, 1]; // Cor laranja (RGBA) para a plataforma que segura a escada
const yellowColor = [0.8, 0.9, 0, 1]; // Cor amarela (RGBA) usada para os faróis dianteiros
const cyanColor = [0.7, 1, 1, 1]; // Cor ciano (RGBA) usada para as janelas da cabine

const commandList = [
    { key: "'h'", description: "Toggle this panel" },
    { key: "'0'", description: "Toggle 1/4 views" },
    { key: "'1'", description: "Front view" },
    { key: "'2'", description: "Left view" },
    { key: "'3'", description: "Top view" },
    { key: "'4'", description: "Axonometric view" },
    { key: "' '", description: "Toggle wireframe/solid" },
    { key: "'q'", description: "Rotate ladder CCW" },
    { key: "'e'", description: "Rotate ladder CW" },
    { key: "'w'", description: "Raise ladder" },
    { key: "'s'", description: "Lower ladder" },
    { key: "'o'", description: "Extend ladder" },
    { key: "'p'", description: "Reduce ladder" },
    { key: "'a'", description: "Move forward" },
    { key: "'d'", description: "Move backward" },
    { key: "'r'", description: "Reset view params" },
    { key: "'ArrowLeft'", description: "Increase theta" },
    { key: "'ArrowRight'", description: "Decrease theta" },
    { key: "'ArrowUp'", description: "Increase gamma" },
    { key: "'ArrowDown'", description: "Decrease gamma" },
    { key: "'j'", description: "Toggle Top Light" },
    { key: "'k'", description: "Toggle left blinker" },
    { key: "'l'", description: "Toggle right blinker" },
    { key: "'n'", description: "Toggle danger lights" }
];

let currentlyOnDisplay = 0;

let leftBlinkerToggle = false;

let rightBlinkerToggle = false;

let dangerLightsToggle = false;

let alternatingLightsToggle = false;

let all_views = true;

let big_view, front_view, left_view, top_view, axo_view;

let projection = mat4();

let zoom = 10;
let aspect = 1.0;

let carPosition = 0; // Posição horizontal do camião. Aumenta ou diminui conforme o camião se move para frente ou para trás.
let LADDER_EXTENSION = 0; // Extensão da escada. Controla o quanto a escada foi estendida 
let LADDER_INCLINATION = 0; // Inclinação da escada. Define o ângulo de elevação ou abaixamento da escada.
let LADDER_BASE_ROTATION = 0;// Rotação da base da escada. Controla o giro da escada em torno de seu ponto de ancoragem,permitindo que ela gire para a esquerda ou direita.
let WHEEL_ROTATION = 0; // Rotação das rodas do camião. Aumenta ou diminui conforme o camião se move, simulando o movimento de rotação das rodas.

let ARROW_LEFT_RIGHT = 0; // Variável para armazenar a rotação horizontal (theta) da câmera, alterada com as setas esquerda/direita para mover a visualização.
let ARROW_UP_DOWN = 0; // Variável para armazenar a rotação vertical (gamma) da câmera, alterada com as setas cima/baixo para ajustar a visualização.



let wireframeOnlyMode = false; //modo contorno inicialmente desativado


//  vistas fixas para as quatro perspectivas
front_view = lookAt(vec3(0, 0, DIST), vec3(0, 0, 0), vec3(0, 1, 0));
left_view = lookAt(vec3(-DIST, 0, 0), vec3(0, 0, 0), vec3(0, 1, 0));
top_view = lookAt(vec3(0, DIST, 0), vec3(0, 0, 0), vec3(0, 0, -1));
axo_view = lookAt(vec3(DIST, DIST, DIST), vec3(0, 0, 0), vec3(0, 1, 0));

big_view = front_view;

/** @type{WebGL2RenderingContext} */
let gl;

/** @type{WebGLProgram} */
let program;

/** @type{HTMLCanvasElement} */
let canvas;

function renderHelpPanel() {
    const helpPanel = document.getElementById("help_panel");
    helpPanel.innerHTML = "<b>Keys:</b><br>";

    // Adicionar cada linha no help pannel
    commandList.forEach(command => {
        helpPanel.innerHTML += `${command.key} : ${command.description}<br>`;
    });
}

function updateModelView(gl, program, modelView) {
    const u_model_view = gl.getUniformLocation(program, "u_model_view");
    gl.uniformMatrix4fv(u_model_view, false, flatten(modelView));
    const u_normals = gl.getUniformLocation(program, "u_normals");
    gl.uniformMatrix4fv(u_normals, false, flatten(normalMatrix(modelView)));
}

function updateProjection(gl, program, projection) {
    const u_projection = gl.getUniformLocation(program, "u_projection");
    gl.uniformMatrix4fv(u_projection, false, flatten(projection));
}



//Alternating color for luz pirilampo
function getAlternatingColor(baseColor, timeMultiplier) {
    let time = (Date.now()) * timeMultiplier;
    let toggle = Math.floor(time) % 2 === 0 ? 1 : 0;  // oscillates between 0 and 1
    let t = baseColor[toggle];
    return t;
}

function resize() {
    canvas.height = window.innerHeight;
    canvas.width = window.innerWidth;
    aspect = window.innerWidth / window.innerHeight;
}

function initialize_objects() {
    CUBE.init(gl);
    SPHERE.init(gl);
    CYLINDER.init(gl);
    PYRAMID.init(gl);
    TORUS.init(gl, 30, 30, WHEEL_RADIUS, WHEEL_WIDTH);
}

function main(shaders) {
    canvas = document.getElementById("gl-canvas");
    gl = setupWebGL(canvas);
    program = buildProgramFromSources(gl, shaders["shader.vert"], shaders["shader.frag"]);

    gl.clearColor(0.5, 0.3, 0.7, 1.0);

    gl.enable(gl.DEPTH_TEST);

    resize();

    renderHelpPanel();

    // Adicionar evento de teclado
    window.addEventListener('keydown', handleKeydown);
    window.addEventListener('resize', resize);
    window.addEventListener("wheel", function (event) {
        zoom *= 1 + (event.deltaY / 1000);
    });

    initialize_objects();

    // This is needed to let wireframe lines to be visible on top of shaded triangles
    gl.enable(gl.POLYGON_OFFSET_FILL);
    gl.polygonOffset(1, 1);

    window.requestAnimationFrame(render);
}
function carBase() {
    multScale([CABIN_x + LOAD_AREA_x + 1, 0.5, CABIN_Z]);
    gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), blackColor);
    updateModelView(gl, program, modelView());
    CUBE.draw(gl, program, gl.LINES)
    gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), redColor);
    updateModelView(gl, program, modelView());
    CUBE.draw(gl, program, wireframeOnlyMode ? gl.LINES : gl.TRIANGLES);
}

function frontBumper() {
    multScale([0.5, LOWER_BASE_y, CABIN_Z]);
    gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), blackColor);
    updateModelView(gl, program, modelView());
    CUBE.draw(gl, program, gl.LINES)
    gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), whiteColor);
    updateModelView(gl, program, modelView());
    CUBE.draw(gl, program, wireframeOnlyMode ? gl.LINES : gl.TRIANGLES);
}

function partAfterFrontBumper() {
    multScale([3, LOWER_BASE_y, CABIN_Z]);
    gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), blackColor);
    updateModelView(gl, program, modelView());
    CUBE.draw(gl, program, gl.LINES)
    gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), whiteColor);
    updateModelView(gl, program, modelView());
    CUBE.draw(gl, program, wireframeOnlyMode ? gl.LINES : gl.TRIANGLES);
}

function redSupportForTheWheels() {
    multScale([2, LOWER_BASE_y, CABIN_Z - 2 * WHEEL_WIDTH]);
    gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), blackColor);
    updateModelView(gl, program, modelView());
    CUBE.draw(gl, program, gl.LINES)
    gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), redColor);
    updateModelView(gl, program, modelView());
    CUBE.draw(gl, program, wireframeOnlyMode ? gl.LINES : gl.TRIANGLES);
}

function middleWhitePart() {
    multScale([6, LOWER_BASE_y, CABIN_Z]);
    gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), blackColor);
    updateModelView(gl, program, modelView());
    CUBE.draw(gl, program, gl.LINES)
    gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), whiteColor);
    updateModelView(gl, program, modelView());
    CUBE.draw(gl, program, wireframeOnlyMode ? gl.LINES : gl.TRIANGLES);
}

function rearBumpers() {
    multScale([1.5, LOWER_BASE_y, CABIN_Z]);
    gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), blackColor);
    updateModelView(gl, program, modelView());
    CUBE.draw(gl, program, gl.LINES)
    gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), whiteColor);
    updateModelView(gl, program, modelView());
    CUBE.draw(gl, program, wireframeOnlyMode ? gl.LINES : gl.TRIANGLES);
}

function frontCabin() {
    multScale([CABIN_x, CABIN_y, CABIN_Z]);
    gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), blackColor);
    updateModelView(gl, program, modelView());
    CUBE.draw(gl, program, gl.LINES)
    gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), redColor);
    updateModelView(gl, program, modelView());
    CUBE.draw(gl, program, wireframeOnlyMode ? gl.LINES : gl.TRIANGLES);
}

function fireFly() {
    multScale([CABIN_x / 4, CABIN_y / 10, CABIN_Z / 5])
    gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), blackColor);
    updateModelView(gl, program, modelView());
    CUBE.draw(gl, program, gl.LINES)
    let baseColor = [[1, 1, 1, 1], [0, 0, 1, 1]];
    let fireflyColor = getAlternatingColor(baseColor, 0.005);
    if (alternatingLightsToggle) {
        gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), fireflyColor);
        updateModelView(gl, program, modelView());
    } else {
        gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), whiteColor);
        updateModelView(gl, program, modelView());
    }
    CUBE.draw(gl, program, wireframeOnlyMode ? gl.LINES : gl.TRIANGLES);
}

function frontWindow() {
    multScale([windowThickness, windowHight, windowLength]);
    gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), blackColor);
    updateModelView(gl, program, modelView());
    CUBE.draw(gl, program, gl.LINES)
    gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), cyanColor);
    updateModelView(gl, program, modelView());
    CUBE.draw(gl, program, wireframeOnlyMode ? gl.LINES : gl.TRIANGLES);
}

function lateralWindow() {
    multScale([windowLength - 3, windowHight, windowThickness]);
    gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), blackColor);
    updateModelView(gl, program, modelView());
    CUBE.draw(gl, program, gl.LINES)
    gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), cyanColor);
    updateModelView(gl, program, modelView());
    CUBE.draw(gl, program, wireframeOnlyMode ? gl.LINES : gl.TRIANGLES);
}

function frontalHeadLights() {
    multScale([frontLightsScale, frontLightsScale, frontLightsScale]);
    gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), yellowColor);
    updateModelView(gl, program, modelView());
    SPHERE.draw(gl, program, gl.LINES)
    gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), yellowColor);
    updateModelView(gl, program, modelView());
    SPHERE.draw(gl, program, wireframeOnlyMode ? gl.LINES : gl.TRIANGLES);
}

function loadingZone() {
    multScale([LOAD_AREA_x, LOAD_AREA_y, LOAD_AREA_z]);
    gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), blackColor);
    updateModelView(gl, program, modelView());
    CUBE.draw(gl, program, gl.LINES)
    gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), redColor);
    updateModelView(gl, program, modelView());
    CUBE.draw(gl, program, wireframeOnlyMode ? gl.LINES : gl.TRIANGLES);
}

function orangePlatForm() {
    multScale([orangePlatformRadius, orangePlatformHight, orangePlatformRadius]);
    gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), blackColor);
    updateModelView(gl, program, modelView());
    CYLINDER.draw(gl, program, gl.LINES)
    gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), orangeColor);
    updateModelView(gl, program, modelView());
    CYLINDER.draw(gl, program, wireframeOnlyMode ? gl.LINES : gl.TRIANGLES);
}

function ladderBoxSupport() {
    multScale([orangePlatformRadius - 1, orangePlatformHight + 0.15, orangePlatformRadius - 1]);
    gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), blackColor);
    updateModelView(gl, program, modelView());
    CUBE.draw(gl, program, gl.LINES)
    gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), greyColor);
    updateModelView(gl, program, modelView());
    CUBE.draw(gl, program, wireframeOnlyMode ? gl.LINES : gl.TRIANGLES);
}

function lateralLadderSupport() {
    multScale(ladderSupportScale);
    gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), blackColor);
    updateModelView(gl, program, modelView());
    CUBE.draw(gl, program, gl.LINES)
    gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), greyColor);
    updateModelView(gl, program, modelView());
    CUBE.draw(gl, program, wireframeOnlyMode ? gl.LINES : gl.TRIANGLES);
}

function ladderSegments() {
    multScale(ladderSegmentScale);
    gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), blackColor);
    updateModelView(gl, program, modelView());
    CUBE.draw(gl, program, gl.LINES)
    gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), greyColor);
    updateModelView(gl, program, modelView());
    CUBE.draw(gl, program, wireframeOnlyMode ? gl.LINES : gl.TRIANGLES);
}

function wheels(pos) {
    multTranslation(pos);
    multRotationX(90);
    multRotationY(WHEEL_ROTATION);
    gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), blackColor);
    updateModelView(gl, program, modelView());
    TORUS.draw(gl, program, gl.LINES)
    gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), whiteColor);
    updateModelView(gl, program, modelView());
    TORUS.draw(gl, program, wireframeOnlyMode ? gl.LINES : gl.TRIANGLES);
}

function insideWheels() {
    multRotationX(90)
    multScale([(WHEEL_RADIUS - WHEEL_WIDTH) * 2, CABIN_Z, (WHEEL_RADIUS - WHEEL_WIDTH) * 2]);
    gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), blackColor);
    updateModelView(gl, program, modelView());
    CYLINDER.draw(gl, program, gl.LINES)
    gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), greyColor);
    updateModelView(gl, program, modelView());
    CYLINDER.draw(gl, program, wireframeOnlyMode ? gl.LINES : gl.TRIANGLES);
}
function mirrowSupport() {
    multScale([0.3, 0.1, 0.6]);
    gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), blackColor);
    updateModelView(gl, program, modelView());
    CUBE.draw(gl, program, gl.LINES);
    gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), blackColor);
    updateModelView(gl, program, modelView());
    CUBE.draw(gl, program, wireframeOnlyMode ? gl.LINES : gl.TRIANGLES);
}

function mirrow() {
    multScale([1, 3, 1]);
    gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), blackColor);
    updateModelView(gl, program, modelView());
    CUBE.draw(gl, program, gl.LINES);
    gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), blackColor);
    updateModelView(gl, program, modelView());
    CUBE.draw(gl, program, wireframeOnlyMode ? gl.LINES : gl.TRIANGLES);
    pushMatrix();
    multTranslation([1, 0, 0]);
    multScale([0.3, 0.8, 1]);
    gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), blackColor);
    updateModelView(gl, program, modelView());
    CUBE.draw(gl, program, gl.LINES);
    gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), cyanColor);
    updateModelView(gl, program, modelView());
    CUBE.draw(gl, program, wireframeOnlyMode ? gl.LINES : gl.TRIANGLES);
}

// Função para atualizar as transformações do carro com base na imagem
function draw_car() {

    //parte relativa ao carro inteiro
    pushMatrix();
    // Aplicar a posição do carro
    multTranslation([carPosition, 0, 0]);

    pushMatrix();//parte relativa À base do carro
    multTranslation([0, baseTranslationY, 0]);
    // Base do caminhão
    pushMatrix();
    carBase();
    popMatrix();

    // Para chockes da frente branco
    pushMatrix();
    multTranslation([-7.3, whiteBaseTranslationY, 0]);
    frontBumper();
    popMatrix();

    // Peça asseguir do para chockes branco
    pushMatrix();
    multTranslation([-5.5, whiteBaseTranslationY, 0]);
    partAfterFrontBumper();
    popMatrix();

    // Peça vermelha a segurar as rodas da frente
    pushMatrix();
    multTranslation([-3, whiteBaseTranslationY, 0]);
    redSupportForTheWheels();
    popMatrix();

    // Peça branca do meio
    pushMatrix();
    multTranslation([1, whiteBaseTranslationY, 0]);
    middleWhitePart();
    popMatrix();

    // Peça vermelha a segurar as rodas de tras
    pushMatrix();
    multTranslation([5, whiteBaseTranslationY, 0]);
    redSupportForTheWheels();
    popMatrix();

    // Para chockes de tras branco
    pushMatrix();
    multTranslation([6.75, whiteBaseTranslationY, 0]);
    rearBumpers();
    popMatrix();

    pushMatrix();//parte relativa as rodas do carro

    const wheelPositions = [
        [frontWheelsX, wheelsPartTranslationY, WheelsZ],//roda  canto inferior esquerdo
        [frontWheelsX, wheelsPartTranslationY, -WheelsZ], //roda canto superior esquerdo
        [backWheelsX, wheelsPartTranslationY, -WheelsZ],//roda  canto superior direito
        [backWheelsX, wheelsPartTranslationY, WheelsZ],//roda  canto inferior direito
    ];
    wheelPositions.forEach(pos => {

        pushMatrix();
        wheels(pos);
        popMatrix();

    });

    //parte DE DENTRO DAs rodas da frente
    pushMatrix();
    multTranslation([frontWheelsX, wheelsPartTranslationY, 0]);
    insideWheels();
    popMatrix();

    //parte DE DENTRO DAs rodas de tras
    pushMatrix();
    multTranslation([backWheelsX, wheelsPartTranslationY, 0]);
    insideWheels();
    popMatrix();

    popMatrix();//parte relativa as rodas do carro
    popMatrix();//parte relativa À base do carro

    pushMatrix();//parte relativa À cabine do carro
    multTranslation([-4.75, 5.25, 0]);

    //cabine da frente
    pushMatrix();
    frontCabin();
    popMatrix();

    //espelho retrovisor direito
    pushMatrix();
    multTranslation([-2, 0, -2.8]);
    mirrowSupport();
    pushMatrix();
    multTranslation([0, 0, -1]);
    mirrow();
    popMatrix();
    popMatrix();
    popMatrix();

    //espelho retrovisor esquerdo
    pushMatrix();
    multTranslation([-2, 0, 2.8]);
    mirrowSupport();
    pushMatrix();
    multTranslation([0, 0, 1]);
    mirrow();
    popMatrix();
    popMatrix();
    popMatrix();


    //luz pirilampo
    pushMatrix();
    multTranslation([-1, 2.75, 0]);
    fireFly();
    popMatrix();


    //janela da frente
    pushMatrix();
    multTranslation([-2, widnowTranslationY, 0]);
    frontWindow();
    popMatrix();

    //janela da esquerda
    pushMatrix();
    multTranslation([-1, widnowTranslationY, 2.5]);
    lateralWindow();
    popMatrix();

    // Janela da direita
    pushMatrix();
    multTranslation([-1, widnowTranslationY, -2.5]);
    lateralWindow();
    popMatrix();

    // farois da frente
    pushMatrix();
    multTranslation([-2, -1.5, -2]);
    frontalHeadLights();
    popMatrix();
    pushMatrix();
    multTranslation([-2, -1.5, 2]);
    frontalHeadLights();
    popMatrix();

    //blinkers
    pushMatrix();
    multTranslation([-2, -2.25, -2.4]);
    multScale([blinkerSize, blinkerSize, blinkerSize]);
    gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), blackColor);
    updateModelView(gl, program, modelView());
    CUBE.draw(gl, program, gl.LINES)
    let baseBlinkerColor = [[1, 1, 1, 1], [1, 0.642, 0, 1]];
    let blinkerColor = getAlternatingColor(baseBlinkerColor, 0.001);
    if (dangerLightsToggle) {
        gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), blackColor);
        updateModelView(gl, program, modelView());
        CUBE.draw(gl, program, gl.LINES);
        gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), blinkerColor);
        updateModelView(gl, program, modelView());
        CUBE.draw(gl, program, wireframeOnlyMode ? gl.LINES : gl.TRIANGLES);
        popMatrix();
        pushMatrix();
        multTranslation([-2, -2.25, 2.4]);
        multScale([blinkerSize, blinkerSize, blinkerSize]);
        gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), blackColor);
        updateModelView(gl, program, modelView());
        CUBE.draw(gl, program, gl.LINES)
        gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), blinkerColor);
        updateModelView(gl, program, modelView());
        CUBE.draw(gl, program, wireframeOnlyMode ? gl.LINES : gl.TRIANGLES);
        popMatrix();
    } else {
        if (leftBlinkerToggle) {
            gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), blinkerColor);
            updateModelView(gl, program, modelView());
        } else {
            gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), whiteColor);
            updateModelView(gl, program, modelView());
        }
        CUBE.draw(gl, program, wireframeOnlyMode ? gl.LINES : gl.TRIANGLES);
        popMatrix();
        pushMatrix();
        multTranslation([-2, -2.25, 2.4]);
        multScale([blinkerSize, blinkerSize, blinkerSize]);
        gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), blackColor);
        updateModelView(gl, program, modelView());
        CUBE.draw(gl, program, gl.LINES)
        if (rightBlinkerToggle) {
            gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), blinkerColor);
            updateModelView(gl, program, modelView());
        } else {
            gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), whiteColor);
            updateModelView(gl, program, modelView());
        }
        CUBE.draw(gl, program, wireframeOnlyMode ? gl.LINES : gl.TRIANGLES);
        popMatrix();
    }

    popMatrix();//parte relativa À cabine do carro

    pushMatrix();//parte da carga + escadas
    multTranslation([2.25, 5, 0]);
    // Zona de carga
    pushMatrix();
    loadingZone();
    popMatrix();


    pushMatrix();//parte da rotação da escada
    multTranslation([2.5, 2.75, 0])
    multRotationY(LADDER_BASE_ROTATION);


    //parte laranja que segura escada
    pushMatrix();
    multRotationY(90)
    orangePlatForm();
    popMatrix();


    //caixa cinzenta que segura escada
    pushMatrix();
    multTranslation([0, 1.10, 0]);
    ladderBoxSupport();
    popMatrix();


    pushMatrix();//parte da inclinação da escada
    multRotationZ(LADDER_INCLINATION);

    //parte da esquerda da escada de baixo
    pushMatrix();
    multTranslation([-5, 0.75, 1]);
    lateralLadderSupport();
    popMatrix();

    //parte da direita da escada de baixo
    pushMatrix();
    multTranslation([-5, 0.75, -1]);
    lateralLadderSupport();
    popMatrix();

    //segmentos da escada de baixo
    for (let i = 0; i < LADDER_SEGMENTS; i++) {
        pushMatrix();
        multTranslation([-9 + i, 0.75, 0]);
        ladderSegments();
        popMatrix();
    }


    pushMatrix();//parte da extensao da escada
    multTranslation([LADDER_EXTENSION, 0, 0])
    //parte da esquerda da escada de cima
    pushMatrix();
    multTranslation([-7, 1.25, 1]);
    lateralLadderSupport();
    popMatrix();

    //parte da direita da escada de cima
    pushMatrix();
    multTranslation([-7, 1.25, -1]);
    lateralLadderSupport();
    popMatrix();

    //parte dos degraus da escada de baixo
    //pushMatrix();
    for (let i = 0; i < LADDER_SEGMENTS; i++) {
        pushMatrix();
        multTranslation([-11 + i, 1.25, 0]);
        ladderSegments();
        popMatrix();
    }
    popMatrix();
    popMatrix();//parte da rotação da escada
    popMatrix();//parte da inclinação da escada
    popMatrix();// parte da extensao da escada
    pushMatrix();//parte relativa a carga + escada



    popMatrix();
    popMatrix();
    popMatrix();// parte relativa ao  carro inteiro
}

// Desenhar chão com padrão de xadrez
function draw_floor() {
    for (let x = -floorLength / 2; x <= floorLength / 2; x++) {
        for (let z = -floorLength / 2; z <= floorLength / 2; z++) {
            pushMatrix();
            multTranslation([x, 0, z]);
            multScale([1, 0.1, 1]);
            updateModelView(gl, program, modelView());
            const color = (x + z) % 2 === 0 ? [0.8, 0.8, 0.8, 1] : [0.3, 0.3, 0.3, 1];
            gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), blackColor);
            updateModelView(gl, program, modelView());
            CUBE.draw(gl, program, gl.LINES)
            gl.uniform4fv(gl.getUniformLocation(program, "u_base_color"), color);
            CUBE.draw(gl, program, gl.TRIANGLES); // Desenhar cubo do chão
            popMatrix();
        }
    }
}

// Modificar a função draw_scene para incluir o carro e o chão
function draw_scene(view) {
    gl.useProgram(program);

    projection = ortho(-aspect * zoom, aspect * zoom, -zoom, zoom, -100, 100);
    updateProjection(gl, program, projection);

    loadMatrix(view);

    draw_floor();
    draw_car();
}

// Função para processar comandos de teclado
function handleKeydown(event) {
    switch (event.key) {
        case 'h': const helpPanel = document.getElementById("help_panel"); helpPanel.style.display = helpPanel.style.display === "none" ? "block" : "none"; break;
        case '0': all_views = !all_views; break;
        case '1': big_view = front_view; currentlyOnDisplay = 1; break;
        case '2': big_view = left_view; currentlyOnDisplay = 2; break;
        case '3': big_view = top_view; currentlyOnDisplay = 3; break;
        case '4': big_view = axo_view; currentlyOnDisplay = 4; break;
        case ' ': wireframeOnlyMode = !wireframeOnlyMode; break;
        case 'q': LADDER_BASE_ROTATION += 5; break;
        case 'e': LADDER_BASE_ROTATION -= 5; break;
        case 'w': if (LADDER_INCLINATION > -45) LADDER_INCLINATION -= 2.5; break;
        case 's': if (LADDER_INCLINATION < 0) LADDER_INCLINATION += 2.5; break;
        case 'o': if (LADDER_EXTENSION >= -7) LADDER_EXTENSION -= 0.1; break;
        case 'p': if (LADDER_EXTENSION <= 0) LADDER_EXTENSION += 0.1; break;
        case 'a': if (carPosition > -5.5) { carPosition -= 0.5; WHEEL_ROTATION -= 45; } break; // Mover o carro para a frente
        case 'd': if (carPosition < 5.5) { carPosition += 0.5; WHEEL_ROTATION += 45; } break; // Mover o carro para trás
        case 'r': axo_view = lookAt(vec3(DIST, DIST, DIST), vec3(0, 0, 0), vec3(0, 1, 0)); ARROW_UP_DOWN = 0; ARROW_LEFT_RIGHT = 0; if (currentlyOnDisplay == 4 || all_views) big_view = axo_view; break;
        case 'ArrowUp': ARROW_UP_DOWN = Math.min(ARROW_UP_DOWN + 10, 89);; // Limita a inclinação máxima a 89º
            axo_view = lookAt(vec3(DIST * Math.sin(ARROW_LEFT_RIGHT * Math.PI / 180), DIST * Math.sin(ARROW_UP_DOWN * Math.PI / 180), DIST * Math.cos(ARROW_LEFT_RIGHT * Math.PI / 180)), vec3(0, 0, 0), vec3(0, 1, 0));
            if (currentlyOnDisplay == 4 || all_views) big_view = axo_view; break;
        case 'ArrowDown': ARROW_UP_DOWN = Math.max(ARROW_UP_DOWN - 1, 0); // Limita a inclinação mínima a 0
            axo_view = lookAt(vec3(DIST * Math.sin(ARROW_LEFT_RIGHT * Math.PI / 180), DIST * Math.sin(ARROW_UP_DOWN * Math.PI / 180), DIST * Math.cos(ARROW_LEFT_RIGHT * Math.PI / 180)), vec3(0, 0, 0), vec3(0, 1, 0));
            if (currentlyOnDisplay == 4 || all_views) big_view = axo_view; break;
        case 'ArrowLeft': ARROW_LEFT_RIGHT += 1;
            axo_view = lookAt(vec3(DIST * Math.cos(ARROW_LEFT_RIGHT * Math.PI / 180), DIST * Math.sin(ARROW_UP_DOWN * Math.PI / 180), DIST * Math.sin(ARROW_LEFT_RIGHT * Math.PI / 180)), vec3(0, 0, 0), vec3(0, 1, 0));
            if (currentlyOnDisplay == 4 || all_views) big_view = axo_view; break;
        case 'ArrowRight': ARROW_LEFT_RIGHT -= 1;
            axo_view = lookAt(vec3(DIST * Math.cos(ARROW_LEFT_RIGHT * Math.PI / 180), DIST * Math.sin(ARROW_UP_DOWN * Math.PI / 180), DIST * Math.sin(ARROW_LEFT_RIGHT * Math.PI / 180)), vec3(0, 0, 0), vec3(0, 1, 0));
            if (currentlyOnDisplay == 4 || all_views) big_view = axo_view; break;
        case 'j': alternatingLightsToggle = !alternatingLightsToggle; break;
        case 'k': if (!rightBlinkerToggle) leftBlinkerToggle = !leftBlinkerToggle; break;
        case 'l': if (!leftBlinkerToggle) rightBlinkerToggle = !rightBlinkerToggle; break;
        case 'n': dangerLightsToggle = !dangerLightsToggle; break;
    }
}

function draw_views() {
    let hw = canvas.width / 2;
    let hh = canvas.height / 2;

    if (all_views) {
        // Draw on front view
        gl.viewport(0, hh, hw, hh);
        draw_scene(front_view);

        // Draw on top view
        gl.viewport(0, 0, hw, hh);
        draw_scene(top_view);

        // Draw on left view
        gl.viewport(hw, hh, hw, hh);
        draw_scene(left_view);

        // Draw of 4th view
        gl.viewport(hw, 0, hw, hh);
        draw_scene(axo_view);
    }
    else {
        gl.viewport(0, 0, canvas.width, canvas.height);
        draw_scene(big_view);
    }
}

function render() {
    window.requestAnimationFrame(render);

    gl.clear(gl.COLOR_BUFFER_BIT | gl.DEPTH_BUFFER_BIT);
    draw_views();
}

loadShadersFromURLS(["shader.vert", "shader.frag"]).then(shaders => main(shaders));
