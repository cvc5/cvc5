export class BaseUndo {
    nodes: number[];
    name: string;

    constructor(nodes: number[], name: string) {
        this.nodes = nodes;
        this.name = name;
    }
}

export class MoveUndo extends BaseUndo {
    x: number;
    y: number;

    constructor(nodes: number[], x: number, y: number) {
        super(nodes, 'MoveUndo');
        this.x = x;
        this.y = y;
    }
}

export class ColorUndo extends BaseUndo {
    colorMap: { [color: string]: number[] };

    constructor(nodes: number[], color: { [color: string]: number[] }) {
        super(nodes, 'ColorUndo');
        this.colorMap = color;
    }
}

export class UnfoldUndo extends BaseUndo {
    positions: { id: number; x: number; y: number }[];
    colors: { id: number; color: string }[];

    constructor(
        nodes: number[],
        positions: { id: number; x: number; y: number }[],
        colors: { id: number; color: string }[],
    ) {
        super(nodes, 'UnfoldUndo');
        this.positions = positions;
        this.colors = colors;
    }
}

export class FoldUndo extends BaseUndo {
    positions: { id: number; x: number; y: number }[];

    constructor(nodes: number[], positions: { id: number; x: number; y: number }[]) {
        super(nodes, 'FoldUndo');
        this.positions = positions;
    }
}

export class HideUndo extends BaseUndo {
    positions: { id: number; x: number; y: number }[];
    nPiNodes: number;

    constructor(nodes: number[], positions: { id: number; x: number; y: number }[], nPiNodes: number) {
        super(nodes, 'HideUndo');
        this.positions = positions;
        this.nPiNodes = nPiNodes;
    }
}
