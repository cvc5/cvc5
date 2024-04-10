export const colorConverter = (colorName: string): string => {
    let color = '#fff';
    switch (colorName) {
        case 'red':
            color = '#f72b34';
            break;
        case 'orange':
            color = '#ff8334';
            break;
        case 'yellow':
            color = '#ffc149';
            break;
        case 'green':
            color = '#60aa51';
            break;
        case 'blue':
            color = '#0097e4';
            break;
        case 'purple':
            color = '#a73da5';
            break;
        case 'brown':
            color = '#a95a49';
            break;
        case 'black':
            color = '#464646';
            break;

        case 'white':
            color = '#f0f0f0';
            break;
    }
    return color;
};
